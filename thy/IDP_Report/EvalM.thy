(*<*)
theory EvalM
imports Main "../LOFT/Examples/SQRL/SQRL_Router"
begin
(*>*)

section\<open>Re-evaluation of Iptables Service Matrix Generation\<close>
text_raw\<open>\label{sec:evalm}\<close>
text\<open>
\todo{A few toy examples first, then SQRL router. Then maybe one of corny's docker things?}
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

(*<*)
end
(*>*)
