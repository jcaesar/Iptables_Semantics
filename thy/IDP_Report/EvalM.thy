(*<*)
theory EvalM
imports Main "../LOFT/Examples/SQRL/SQRL_Router" "../Iptables_Semantics/Examples/Example_IPPart_Routing"
begin
(*>*)

section\<open>Re-evaluation of Iptables Service Matrix Generation\<close>
text_raw\<open>\label{sec:evalm}\<close>
text\<open>
We will begin with a few toy examples that demonstrate in what kind of cases interface rewriting
is useful when generating service matrices. After that, we show two real-world examples
of improvements of service matrices through interface rewriting.
\<close>
text\<open>
As a first, truly minimal example (that is still within our validity criteria for configurations)
we will take a device with a single routing rule\footnote{Albeit nonsensical, this rule is actually accepted by the Linux kernel.}:
\begin{lstlisting}[basicstyle=\ttfamily\small,breaklines=true]
default dev eth0 scope link
\end{lstlisting}
and a single entry in the \texttt{FORWARD} chain (with a \texttt{DROP} default policy)
\begin{lstlisting}[basicstyle=\ttfamily\small,breaklines=true]
-A FORWARD -o eth1 -j ACCEPT 
\end{lstlisting}
Obviously, we cannot infer anything about the behavior of this firewall if we only examine the iptables configuration.
Accordingly, if we run the service matrix generation without any additional info,
it will give us a useless upper bound of a firewall accepting all packets.
If we additionally consider the routing table, we know that all packets get routed to \texttt{eth0},
but since the firewall only accepts packets to \texttt{eth1}, all packets get dropped.
Accordingly, if we pass the routing table to the service matrix generation,
it will give use an empty result, indicating that all traffic is (guaranteed to be) dropped.
This minimal example also shows why it is crucial to consider all interfaces when generating the
routing relation, as explained in Section~\ref{sec:routing_ipass}.
Had we not added an empty entry for \texttt{eth1}, the result of the interface rewriting would be its input.

While the first example is truly minimal, it is also clearly synthetic.
A more realistic configuration might have a routing table like this:
\begin{lstlisting}[basicstyle=\ttfamily\small,breaklines=true]
default via 10.0.2.1 dev eth2 src 10.0.2.2 metric 202 
10.0.1.0/24 dev eth1 proto kernel scope link src 10.0.1.1
10.0.2.0/24 dev eth2 proto kernel scope link src 10.0.2.2 metric 202
\end{lstlisting}
and a (default drop) \texttt{FORWARD} chain like
\begin{lstlisting}[basicstyle=\ttfamily\small,breaklines=true]
-A FORWARD -m conntrack --ctstate RELATED,ESTABLISHED -j ACCEPT
-A FORWARD -i eth1 -o eth2 -j ACCEPT
\end{lstlisting}
Again, it is clear that we cannot infer anything about the behavior of this configuration
w.r.t. the IP space with only the information from the \texttt{FORWARD} chain.
However, for our tools to be able to fully understand this firewall,
it is necessary to not only provide the routing table, but also an IP assignment for the input interfaces:
@{thm [display] (rhs) assmt2_def[unfolded Let_def]}
If we apply rewriting with this IP assignment and the routing table, we obtain
the result we desired, as shown in Figure~\ref{fig:ex2_full}.
\<close>
text_raw\<open>
\begin{figure}
\centering
\input{figures/ex2_full.tex}
\caption{Second example access matrix with rewriting}
\label{fig:ex2_full}
\end{figure}
\<close>
subsection\<open>Real World Example 1\<close>
text_raw\<open>\label{sec:sqrlfweval}\<close>
text\<open>
Our first example based on a real-world firewall configuration is a re-implementation of Firewall D
from \cite{diekmann2016verified}.
As this is firewall configuration is deployed on a router-like device, we analyze the \texttt{FORWARD}-chain
of the \texttt{filter} table.

While the shorewall-based implementation has been replaced by a manual implementation,
its style and intent have not been changed.
The intention of the firewall is to group the clients and sub-networks into different classes.
Some networks are ``trusted'' and get full access to each other and the internet.
Other networks are various degrees ``untrusted'' and only get access to the internet,
with some special rules on whether the ``trusted'' network gets access to them and to how much of the internet
they get access.
Since the firewall does not make heavy use of rules that are based on layer 4 port matches,
we will only analyze a single protocol and source and destination port combination.
We arbitrarily decided on TCP with source port 10000 and destination port 80.
A thorough analysis needs to consider at least a few ports more.

We load the \texttt{filter} table as a constant: @{const SQRL_fw}.
As before, the firewall still wires (groups of) interfaces together in the filter table,
 operating as a kind of link-layer firewall.
The first (two) rules from the \texttt{FORWARD} and \texttt{FromInternalF} chains are:
\begin{quote}
 \texttt{-A FORWARD -i lup -m state --state RELATED,ESTABLISHED -j ACCEPT} \\
 \texttt{-A FORWARD -i lmd -j FromInternalF} \\
 \texttt{-A FromInternalF -o lmd -j ACCEPT} \\
\end{quote}
Consequently, if we abstract over interfaces without providing any additional information,
this will be rewritten to a rule accepting all packets.
The resulting service matrix for  is shown in Figure~\ref{fig:sqrl_rtr_none}.
While this service matrix is a correct overapproximation of the set of allowed packets, 
as such it is devoid of any information.
\<close>
text_raw\<open>
\begin{figure}
\centering
\input{figures/sqrl_rtr_none.tex}
\caption{Access matrix for Firewall D without interface rewriting}
\label{fig:sqrl_rtr_none}
\end{figure}
\<close>
text\<open>
As explained Chapter~\ref{chap:implementation}, we need an input interface IP assignment
and the main routing table.
Firewall D happens to meet the condition of only having one routing table that handles all non-local traffic
and we can directly import it as @{const SQRL_rtbl_main}.
Instead of using reverse path filtering, spoofing protection is implemented manually in the \texttt{raw}-table.
As discussed, the source interface has to be manually specified:
@{thm[break,display] ipassmt_def[unfolded Let_def prod.case]}
While this IP assignment is slightly more strict than what even strict reverse path filtering
would have provided, it also poses a danger:
the correctness result of the rewriting process requires the absence of spoofed packets, i.e.
we can obtain faulty results by providing a broken IP assignment
that states smaller IP ranges than actually permitted.
Fortunately, we can use the tools introduced with \cite{diekmann2015cnsm}
to certify that spoofing protection wrt. @{const ipassmt} is actually guaranteed.
We load the raw table as @{const SQRL_raw} and verify that spoofing protection is given%
\footnote{If we didn't specify the IP assignment in Isabelle,
we could also use the standalone tool, 
with an invocation along the lines of 
\texttt{\$ fffuu --ipassmt ipassmt\_file --table raw --chain PREROUTING iptables-save}}:
\<close>
text_raw\<open>
\begin{figure}
\centering
\input{figures/sqrl_rtr_full.tex}
\caption{Access matrix for Firewall D with full interface rewriting}
\label{fig:sqrl_rtr_full}
\end{figure}
\<close>
lemma "\<forall>(ifce, _) \<in> set ipassmt. 
  (no_spoofing_iface ifce (map_of_ipassmt ipassmt)
    (upper_closure (unfold_ruleset_CHAIN 
      ''PREROUTING'' SQRL_raw_PREROUTING_default_policy   (map_of_string_ipv4 SQRL_raw))))" 
by (fact sqrl_spoof_protection)
text\<open>With that, we can directly apply our machinery and obtain a detailed service matrix
as shown in Figure~\ref{fig:sqrl_rtr_full}.
The two IP spaces on the bottom row represent the internet, 
fragmented into one set that only contains a Debian update server and a CI server, and the rest.
The three IP spaces in the middle row are the ``untrusted'' networks, 
and the networks on the top row are the ``trusted'' network, and the rest of the \texttt{10.0.0.0/8}
network that is not being routed. (Part of that unrouted space is occupied by a management VPN.)
The service matrix shows that the device does display the intended behavior (at least for that specific port).
\<close>
text_raw\<open>
\begin{figure}
\centering
\input{figures/sqrl_rtr_assmt.tex}
\caption{Access matrix for Firewall D with input interface rewriting}
\label{fig:sqrl_rtr_assmt}
\end{figure}
\<close>
text\<open>
While Figure~\ref{fig:sqrl_rtr_full} concludes the analysis, 
we can also use this example to get some evidence towards a suspicion we had:
from the intuition we gained from manual inspection of firewall rulesets,
we thought that, for typical firewall rulsets, more information is lost when 
abstracting over input interfaces than when abstracting over output interfaces.
Figure~\ref{fig:sqrl_rtr_rtbl} shows the access matrix as before, but only with
output interface rewriting, Figure~\ref{fig:sqrl_rtr_assmt} only with input interface rewriting.
The two figures do seem to confirm our intuition, but only in this special case.
This might be different for rulesets that implement blacklisting or rulesets that allow
access less based on who is accessing and more on what is being accessed.
That being said, neither of the two figures holds enough information to be sure
that the device displays the intended behavior.
\<close>
text_raw\<open>
\begin{figure}
\centering
\input{figures/sqrl_rtr_rtbl.tex}
\caption{Access matrix for Firewall D with output interface rewriting}
\label{fig:sqrl_rtr_rtbl}
\end{figure}
\<close>
section\<open>Real World Example 2\<close>
text_raw\<open>\label{sec:evaldocker}\<close>
text\<open>
As a second example, we show the evaluation of a configuration for a docker container.
Compared to the first example, this example is a lot smaller, which has the advantage
that we can show the configuration dump here for manual inspection of the results.
While the filtering behavior of this configuration is also not based nearly exclusively on the link layer,
we still cannot obtain any interesting results since one of the first rules of the firewall
is to drop \texttt{ACCEPT} all packets from interface \texttt{br-0a5ad9e85c71} that are not sent back
out on the same interface.
We show the entire relevant configuration in Figure~\ref{fig:docka}.
Note that the \texttt{DOCKER} chain is not missing but empty.
\<close>
text_raw\<open>
\begin{figure}
\begin{subfigure}[b]{\textwidth}
\begin{lstlisting}[basicstyle=\ttfamily\scriptsize,breaklines=true]
docker0 = [172.17.0.1/16]
br-0a5ad9e85c71 = [10.0.0.0/8]
\end{lstlisting}
\caption{IP assignment}
\end{subfigure}
\begin{subfigure}[b]{\textwidth} 
\begin{lstlisting}[basicstyle=\ttfamily\scriptsize,breaklines=true]
default via 10.0.2.2 dev enp0s3  proto static  metric 100 
10.0.0.0/8 dev br-0a5ad9e85c71  proto kernel  scope link  src 10.42.0.100 
10.0.2.0/24 dev enp0s3  proto kernel  scope link  src 10.0.2.15  metric 100 
172.17.0.0/16 dev docker0  proto kernel  scope link  src 172.17.0.1
\end{lstlisting}
\caption{\texttt{ip route}}
\end{subfigure}
\begin{subfigure}[b]{\textwidth}
\begin{lstlisting}[basicstyle=\ttfamily\scriptsize,breaklines=true]
-A FORWARD -j DOCKER-ISOLATION
-A FORWARD -o br-0a5ad9e85c71 -j DOCKER
-A FORWARD -o br-0a5ad9e85c71 -m conntrack --ctstate RELATED,ESTABLISHED -j ACCEPT
-A FORWARD -i br-0a5ad9e85c71 ! -o br-0a5ad9e85c71 -j ACCEPT
-A FORWARD -j DFWFW_FORWARD
-A FORWARD -o docker0 -j DOCKER
-A FORWARD -o docker0 -m conntrack --ctstate RELATED,ESTABLISHED -j ACCEPT
-A FORWARD -i docker0 ! -o docker0 -j ACCEPT
-A FORWARD -i docker0 -o docker0 -j ACCEPT
-A FORWARD -i br-0a5ad9e85c71 -o br-0a5ad9e85c71 -j DROP
-A DFWFW_FORWARD -m state --state INVALID -j DROP
-A DFWFW_FORWARD -m state --state RELATED,ESTABLISHED -j ACCEPT
-A DFWFW_FORWARD -s 10.0.0.1/32 -d 10.0.0.1/32 -i br-0a5ad9e85c71 -o br-0a5ad9e85c71 -j ACCEPT
-A DFWFW_FORWARD -s 10.0.0.1/32 -d 10.0.0.2/32 -i br-0a5ad9e85c71 -o br-0a5ad9e85c71 -j ACCEPT
-A DFWFW_FORWARD -s 10.0.0.1/32 -d 10.0.0.4/32 -i br-0a5ad9e85c71 -o br-0a5ad9e85c71 -j ACCEPT
-A DFWFW_FORWARD -s 10.0.0.3/32 -d 10.0.0.3/32 -i br-0a5ad9e85c71 -o br-0a5ad9e85c71 -j ACCEPT
-A DFWFW_FORWARD -s 10.0.0.3/32 -d 10.0.0.2/32 -i br-0a5ad9e85c71 -o br-0a5ad9e85c71 -j ACCEPT
-A DFWFW_FORWARD -s 10.0.0.3/32 -d 10.0.0.4/32 -i br-0a5ad9e85c71 -o br-0a5ad9e85c71 -j ACCEPT
-A DFWFW_FORWARD -s 10.0.0.2/32 -d 10.0.0.2/32 -i br-0a5ad9e85c71 -o br-0a5ad9e85c71 -j ACCEPT
-A DFWFW_FORWARD -s 10.0.0.4/32 -d 10.0.0.1/32 -i br-0a5ad9e85c71 -o br-0a5ad9e85c71 -j ACCEPT
-A DFWFW_FORWARD -s 10.0.0.4/32 -d 10.0.0.3/32 -i br-0a5ad9e85c71 -o br-0a5ad9e85c71 -j ACCEPT
-A DFWFW_FORWARD -s 10.0.0.4/32 -d 10.0.0.2/32 -i br-0a5ad9e85c71 -o br-0a5ad9e85c71 -j ACCEPT
-A DFWFW_FORWARD -s 10.0.0.4/32 -d 10.0.0.4/32 -i br-0a5ad9e85c71 -o br-0a5ad9e85c71 -j ACCEPT
-A DFWFW_FORWARD -j DROP
-A DFWFW_INPUT -i br-0a5ad9e85c71 -j DROP
-A DFWFW_INPUT -i docker0 -j DROP
-A DOCKER-ISOLATION -i docker0 -o br-0a5ad9e85c71 -j DROP
-A DOCKER-ISOLATION -i br-0a5ad9e85c71 -o docker0 -j DROP
-A DOCKER-ISOLATION -j RETURN
\end{lstlisting}
\caption{Forwarding-relevant part of \texttt{iptables-save}}
\end{subfigure}
\caption{Firewall configuration for docker container}
\label{fig:docka}
\end{figure}
\<close>
text\<open>
We show the generated access matrices in Figures~\ref{fig:dockeracc}.
What follows is an analysis of the configuration assisted by the service matrices,
but without any detailed knowledge towards the intent of the configuration.
We can clearly see the fine-grained configuration for four hosts in
\texttt{10.0.0.0/30} with their access to each other and the Internet.
The \texttt{10.0.2.0/24} network, accessable from everywhere in \texttt{10.0.0.0/8}, 
seems to be some kind of transit network.
We can also see that the rest of the \texttt{10.0.0.0/8} network that is not being used
shut off and can't be accessed from anywhere,
probably in case anything new hosts come up but aren't fully configured.
The \texttt{172.17.0.0/16} network is entirely shut off, the reasons for that are not clear to us.
\<close>
text_raw\<open>
\begin{figure}
\centering
\begin{subfigure}[b]{\textwidth}
\centering
\input{figures/docker_none.tex}
\caption{No interface rewriting}
\end{subfigure}
\begin{subfigure}[b]{\textwidth}
\centering
\input{figures/docker_full.tex}
\caption{Full interface rewriting}
\end{subfigure}
\caption{Access matrix for docker container configuration}
\label{fig:dockeracc}
\end{figure}
\<close>
text\<open>These examples have clearly demonstrated that interface rewriting can be crucial 
for interesting analysis results about some firewalls.\<close>

(*<*)
end
(*>*)
