#!/usr/bin/python

from mininet.net import Mininet
from mininet.topo import Topo
from mininet.link import TCLink
from mininet.cli import CLI
from mininet.util import quietRun
from mininet.log import setLogLevel, info, output, debug, error, lg, LEVELS # I'm not sure I'm using lg and LEVELS right. If they cause trouble, remove them. They're just here for slightly more beautiful output
from mininet.term import makeTerms
from mininet.node import Host, OVSBridge, OVSSwitch, RemoteController
from mininet.util import waitListening

import monotonic # needs python-monotonic
from random import randint, shuffle
from sys import exit, stdin, argv
from re import findall
from time import sleep
import os
import struct, socket
import signal

ip2int = lambda ipstr: struct.unpack('!I', socket.inet_aton(ipstr))[0]
int2ip = lambda n: socket.inet_ntoa(struct.pack('!I', n))

def pne(s):
	if not s.strip() == "":
		if not "\n" in s:
			s = s + "\n"
		print(s)

def qcall(o,a,*args):
	info('config {}: {}\n'.format(o, args))
	orv = a(*args)
	rv = orv
	if not rv.strip() == "":
		if not "\n" in rv:
			rv = rv + "\n"
		error('{} in {} failed: {}'.format(args, o, rv))
	return orv

class IFCHlp:
	ifcs = [
		('ldit', ("10.13.42.137", 29)),
		('lmd', ("10.13.42.129", 29)),
		('loben', ("10.13.42.145", 28)),
		('lup', ("13.14.15.58", 24)),
		('vocb', ("10.13.43.17", 28)),
		('vpriv', ("10.13.37.200", 24)),
		('vshit', ("10.13.43.1", 28)),
		('wg', ("10.13.41.1", 27)),
		('wt', ("10.13.42.161", 28)),
	] # the order is important. the port numbers will be assigned based on it! (yes, I got it wrong at some point. take a good hard look.)

	def ifc(self):
		for (iface, ipsn) in self.ifcs:
			self.intf('s1-' + iface).setIP(*ipsn)

class StaticSwitch(OVSSwitch,IFCHlp): # Bridge is closest to what we want. It quacks like it.
	batch = False
	requirecommonnet=True
	@classmethod
	def addSelf(cls, name, topo):
		return topo.addSwitch(name, ip=None, cls=StaticSwitch)
	@classmethod
	def batchStartup(cls, switches, *_parm, **_parms):
		rv = OVSSwitch.batchStartup(switches, *_parm, **_parms)
		for s in switches:
			s.poststart()
		return rv
	def poststart(self):
		self.ifc()
		flows = [
			"'table=0,hard_timeout=0,idle_timeout=0,priority=2,arp,action=flood'",
			"'table=0,hard_timeout=0,idle_timeout=0,priority=2,ipv4,ct_state=-trk,action=ct(table=1,zone=42)'",
			"'table=0,hard_timeout=0,idle_timeout=0,priority=2,ipv6,action=drop'", # just so you can see what's being dropped, and why.
			"'table=0,hard_timeout=0,idle_timeout=0,priority=1,action=drop'",

			"'table=1,hard_timeout=0,idle_timeout=0,priority=2,ip,ct_state=+trk+new,action=goto_table:2'",
			"'table=1,hard_timeout=0,idle_timeout=0,priority=2,ip,ct_state=+trk+est,action=goto_table:3'",
			"'table=1,hard_timeout=0,idle_timeout=0,priority=1,action=drop'",
		]
		with open('sqrl_of_new.txt') as f:
			    for line in f:
					line = line.replace('action=output', 'action=ct(commit,zone=42),output') # cheating!
					line = line.replace('\n', "'")
					flows.append("'table=2," + line);
		with open('sqrl_of_est.txt') as f:
			    for line in f:	
					line = line.replace('\n', "'")
					flows.append("'table=3," + line);
		for f in flows:
			qcall(self,self.dpctl,"add-flow", f)

class DRtr(Host,IFCHlp):
	requirecommonnet=False
	@classmethod
	def addSelf(cls, name, topo):
		return topo.addHost(name, ip=None, cls=DRtr)
	def config(self, *_parm, **_params):
		rv = Host.config(self, *_parm, **_params)
		qcall(self,self.cmd, "sed <iptables-save 's/-i /-i s1-/; s/-o /-o s1-/;' | iptables-restore")
		self.ifc()
		self.cmd('sysctl -w net.ipv4.ip_forward=1')
		return rv
	def terminate(self):
		self.cmd('sysctl net.ipv4.ip_forward=0')
		Host.terminate(self)

class DTopo(Topo):
	"""Topology for Test:
	   client - router - internet (actually, the internet is just a single box...)"""
	def __init__(self, scls):
		self.scls = scls
		return Topo.__init__(self)
	def build(self):
		commonnet = None;
		if self.scls.requirecommonnet:
			commonnet = '5'
		switch = self.scls.addSelf('s1', topo=self)
		for (iface, (ip, net)) in IFCHlp.ifcs:
			name = 'h' + iface
			mip = int2ip(ip2int(ip) + 1) # just assume that there's another IP in that net, directly next. Should fail soon if untrue...
			mnet = commonnet or str(net)
			dev = self.addHost(name, ip=mip+'/'+mnet, defaultRoute='via '+ip)
			self.addLink(dev, switch, intfName2='s1-' + iface)
		#client = self.addHost('h1', ip='10.0.1.2/'+net, defaultRoute='via 10.0.1.1')
		#nhsl = self.addLink(nhost,  switch,  intfName2='s1-wan')

def dump(ofile, strng):
	with open(ofile, "w") as fo:
		fo.write(strng.replace("\r\n","\n"))

def tcpreachtest(net, client, server, port=80, timeout=2.5):
	server.cmd("    echo servuer    "); # just to make sure the pipes are clean. I'm not even kidding. :(
	client.cmd("    echo cliuent    ");
	sleep(1);
	ts = monotonic.monotonic()
	output("TCP {}: {} -> {}: ".format(port, client, server))
	if lg.isEnabledFor(LEVELS.get('debug')):
		output("\n")
	rand = "{}".format(randint(0,18446744073709551615))
	server.sendCmd("    socat -d -d EXEC:'echo {}' TCP4-LISTEN:{},reuseaddr    ".format(rand,port)) # what are these spaces in front of socat for? well, mininet, the piece of high quality software isn't that precise about its communication with the nodes... occasionally, the first byte gets lost.
	while monotonic.monotonic() - ts < timeout / 2:
		data = server.monitor(timeoutms=50)
		debug("{}\n".format(data.strip()))
		if 'N listening on' in data:
			break
	cliout = client.cmd("    socat TCP:{}:{},connect-timeout={} -    ".format(server.IP(), port, max(timeout - (monotonic.monotonic() - ts), 0.1)))
	server.sendInt()
	servout = server.waitOutput()
	result = cliout.strip() == rand
	output("{}\n".format("success" if result else "fail"))
	debug("tcp test: socat server: {}\n".format(servout.strip()))
	debug("tcp test: socat client: {}\n".format(cliout.strip()))
	debug("tcp test:     expected: {}\n".format(rand))
	server.cmd("    echo servuer    ");
	client.cmd("    echo cliuent    ");
	return result

def tcpreachtests(net, hosts, ports=[80], timeout=2.5):
	if type(ports) is not list:
		ports = [ports]
	tests = []
	for port in ports:
		for h1 in hosts:
			for h2 in hosts:
				if h1 == h2:
					continue
				tests.append((net, h1, h2, port, timeout))
	return tests

def makearpentries(host, hosts):
	# add all arp entries for host to hosts.
	for intf in host.intfList():
		if intf.MAC() and intf.IP(): # will also sort out loopback
			for host in hosts:
				host.cmd("arp -s {} {}".format(intf.IP(), intf.MAC())) # will fail with Netwok unreachable at given times. Easier to ignore than fix.

def standalone():
	args = {}
	for a in argv:
		if ':' in a:
			k,v = a.split(':',1)
			args[k] = v
		else:
			args[a] = None
	ports = [22,80]
	if "ports" in args:
		ports = [int(p) for p in args['ports'].split(',')]
	if "timeout" in args:
		signal.signal(signal.SIGALRM, lambda _1, _2: (error('timeout\n'), exit(-1)))
		signal.alarm(int(args["timeout"] or 42))
	if "debug" in args:
		setLogLevel( 'debug' )
	elif "info" in args:
		setLogLevel( 'info' )
	scls=None
	if "of" in args:
		scls = StaticSwitch 
	elif "lr" in args:
		scls = DRtr
	else:
		print("Supply either of (for OpenFlow) or lr (for a Linux Router)")
		exit(-1)
	topo = DTopo(scls=scls)
	net = Mininet(topo=topo,autoSetMacs=True) # controller=RemoteController
	net.start()
	sw = net.get('s1')
	trabant = net.get(*['h' + ifce for ifce,_ in IFCHlp.ifcs])
	if "noarp" not in args:
		makearpentries(sw, trabant)
	if "dump" in args:
		if "lr" in args:
			dump('iptables-save-dump', sw.cmd('iptables-save'))
			dump('ip-route-dump', sw.cmd('ip route'))
			dump('collectedmacs-dump', sw.cmd('collectmacs.sh'))
	if "test" in args:
		t = args['test']
		if t is None:
			net.ping(trabant)
			for t in shuffle(tcpreachtests(net,trabant,ports=ports)):
				tcpreachtest(*t)	
		else:
			if t == 'ping':
				net.ping(trabant)
			else:
				z,n = [int(a) for a in t.split('/')]
				tests = tcpreachtests(net,trabant,ports=ports)
				s = int((len(tests)-1)/n+1)
				b = z*s
				a = b-s
				output('tcp test fragment {}-{} / {}\n'.format(a+1,b,len(tests)))
				for t in tests[a:b]:
					tcpreachtest(*t)
		if "of" in args and "dump" in args:
			info(sw.dpctl("dump-flows"));
			for ln in sw.cmd("ovs-dpctl", "dump-conntrack").splitlines():
				if "zone=42" in ln:
					output(ln + '\n')
	if "cli" in args:
		net.tcpreachtest = lambda server, client, port: tcpreachtest(net, client, server, port)
		net.setLogLevel = lambda ll: setLogLevel(ll) and None
		CLI(net)
	net.stop()

if __name__ == '__main__':
	standalone()

topos = { 
	'lr': ( lambda: DTopo(scls=DRtr) ), 
	'of': ( lambda: DTopo(scls=StaticSwitch) ),
}
