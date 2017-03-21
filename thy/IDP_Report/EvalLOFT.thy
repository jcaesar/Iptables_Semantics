(*<*)
theory EvalLOFT
imports Main "../LOFT/Examples/SQRL/SQRL_Router"
begin
(*>*)

section\<open>Re-evaluation of LOFT\<close>
text_raw\<open>\label{sec:evalloft}\<close>
text\<open>This section will re-evaluate the results of LOFT~\cite{LOFT-AFP} based on real-world data.
This section assumes basic familiarity with LOFT.
If any details of the explanations are unclear, please refer to the original publication~\cite{LOFT-AFP}.
As a short remainder: LOFT transforms a routing table and a firewall from a Linux device
into two lists of pairs, each pair containing a @{type simple_match} and an action
(either a port to forward to, or one of @{term "{Accept,Drop}"}).
We call this format of a list of pair of match expression and an action of arbitrary type a
generalized (simple) firewall.
The idea is that, in a Linux style router, these two generalized firewalls are considered sequentially
for a routing/forwarding decision.
With that model, we can execute the process shown in Figure~\todo{}:
If we form the cross product of these two firewalls and conjoin the match expression,
we can obtain a single generalized firewalls that computes the same decision in one step.
This single generalized firewalls can easily be converted to an OpenFlow table, with one catch:
the match expressions can match on an output port,
but such a match does not make sense in an OpenFlow table.
Hence, we had to require that the input firewall does not contain output interface matches.
This very fact was another motivation for this work:
if we have output interface rewriting, we can just remove output interface matching without
loosing any information that would be relevant for the forwarding behavior.
We finally wanted to put this to a test on a real-world configuration.
For this purpose, we will reuse the configuration from Section~\ref{sec:sqrlfweval}.
\<close>
text\<open>
However, there is still one problem: the firewall in question uses stateful matches.
When analyzing firewalls in Section~\ref{sec:evalm}, we looked at the behavior for packets that
belong to new connections.
If we build a configuration for a stateful device that only forwards packets as if they were new,
much of the original functionality will likely be lost.
On the other hand, if we permit all packets as if they are in the established state,
we will likely allow too much%
\footnote{We could even compute a firewall that accepts packets if the original firewall would have
accepted them in either one state.
But since configurations tend to accept all established packets if they accept the corresponding new packets,
there is no point in doing so.}.
Given that many firewall configurations start with accepting all packets in established connections,
the resulting configuration will simply forward all packets.
\<close>
text_raw\<open>
\begin{figure}
\begin{verbatim}
			table=0,priority=2,arp,action=flood
			table=0,priority=2,ipv4,ct_state=-trk,action=ct(table=1,zone=42)
			table=0,priority=2,ipv6,action=drop
			table=0,priority=1,action=drop

			table=1,priority=2,ip,ct_state=+trk+new,action=goto_table:2
			table=1,priority=2,ip,ct_state=+trk+est,action=goto_table:3
			table=1,priority=1,action=drop
\end{verbatim}
\caption{OVS rules for separating packets into tables based on state}
\todo{OVS abbreviation}
\label{fig:ovsconntrack}
\end{figure}
\<close>
text\<open>Our solution for this problem is to take a step back:
In this case, we want to experimentally verify a concrete IPv4 only \todo{mention that upstream} configuration transformation
 using Mininite\todo{cite} and OpenVSwitch\todo{cite}.
Instead of clinging to our pure formalization abiding by the OpenFlow\todo{cite} standard,
we recombine our results freely.
OpenVSwitch features the capability to hand packets to the Linux \texttt{conntrack} module
and do stateful matches.
With the set of rules shown in Figure~\ref{fig:ovsconntrack}%
\footnote{The configuration floods ARP requests because the generated tables will only forward IP traffic.}%
$^{\text{,}}$%
\footnote{Since the original device was IPv4 only, we drop IPv6.
We should, in theory, be able to generate two more OpenFlow tables to handle IPv6.}
, it is possible to separate packets
into different tables.
Hence, we simply use our tools to generate two, not one, OpenFlow table, 
one for new and one for established connections and load these into the appropriate tables.
The only thing that is left to do is to slightly modify the ruleset for the table
for new connections: if a packet is accepted and forwarded, update the \texttt{conntrack} state,
i.e. all rules with an action \texttt{output} get an additional action \texttt{ct(commit,zone=42)}.
An overview over this process is shown in Figure~\todo{}.
\<close>
text_raw\<open>
\begin{figure}
\scalebox{0.9}{
\begin{minipage}{\textwidth}
\tiny
@{thm[break] (rhs) SQRL_fw_simple_new_openflow_14} \\
$\ldots$
\end{minipage}
}
\caption{Start of generated OpenFlow table for new packets}
\label{fig:ovsgenerated}
\end{figure}
\<close>
text\<open>As an example, the first fourteen rules of the table for new packets as originally produced by LOFT
 are shown in Figure~\ref{fig:ovsgenerated}.
We have written a script to load both,
the original configuration and the translated OVS configuration into a Mininet environment.
The script also creates one directly attached host per attached interface%
\footnote{We have tested indirectly attached hosts / hosts reachable through another router
in the original LOFT evaluation and did not feel the need to re-evaluate that.}
and we tested reachability, again on TCP port 80%
\footnote{We also tested port 139 and ICMP ping, but the results did not differ},
for all pairs of hosts%
\footnote{Reachability to the device itself is not preserved and we did not test it.}.
The result is shown in Table~\todo{}.
.
\<close>

(*<*)
end
(*>*)
