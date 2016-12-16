(*<*)
theory RPF
imports  "../Routing/ReversePathFiltering" Routing
begin
(*>*)

section\<open>Reverse Path Forwarding\<close>
text_raw\<open>\label{sec:rpf}\<close>
text\<open>Note: This section does not bear any significance for further sections, it is ``merely'' an interesting consideration.\<close>
text\<open>In Section \ref{sec:routing_ipass}, we introduced the IP assignment as a relation
that describes which destination IP addresses can be forwarded to which ports.
Among other things, this section explores IP assignments as the converse:
as a relation that describes which source IP addresses are expected to arrive on which interfaces%
\footnote{Historically, we actually used IP assignments for this first.
The explanation flows smoother in this order.}.
\<close>
text\<open>While source address spoofing takes away any possible way to know
what source addresses can be expected for traffic arriving at interfaces,
there are techniques to discard traffic with source addresses that can immediately be recognized as spoofed
(i.e., recognize traffic tolerating false accepts but trying to avoid false rejects).
These techniques are collected in RFC3704: ``Ingress Filtering for Multihomed Networks''.
Since they are derived from the homonymous techniques for avoiding loops when forwarding multicast traffic\todo{cite?},
they are more commonly known as \emph{Reverse Path Forwarding}%
\footnote{Sometimes erroneously named ``Reverse Path Filtering''.} (RPF).
The information that is necessary for RPF comes from the Forwarding Information Base (FIB).
If we reuse the assumptions we made in Section \ref{sec:realrouting},
the only thing that is relevant is thus the routing table.
We made all definitions of this section based on that assumption.\<close>

text\<open>RFC 3704 defines five ways of implementing RPF:
\begin{itemize}
  \item Ingress Access Lists
  \item Strict Reverse Path Forwarding
    \begin{quote}``The procedure is that the
     source address is looked up in the FIB
     — and if the packet is received on the interface which would be used
     to forward the traffic to the source of the packet, it passes the
     check.''\end{quote}
  \item Feasible Path Reverse Path Forwarding
    \begin{quote}
      ``The source address is still looked up in the FIB (or
      an equivalent, RPF-specific table) but instead of just inserting one
      best route there, the alternative paths (if any) have been added as
      well, and are valid for consideration.''
    \end{quote}
  \item Loose Reverse Path Forwarding
    \begin{quote}
      ``It checks only for the existence of a route (even a default route, if applicable), not where the route points to.''
    \end{quote}
  \item Loose Reverse Path Forwarding ignoring default routes
    \begin{quote}
    ``In the lookup, default routes are excluded.''
    \end{quote}
    (note that there are some variants defined in the RFC.)
\end{itemize}
The first item, Ingress Access Lists, just means to specify a list of acceptable source addresses for each interface.
In other words, it requires the user to statically specify the source IP assignment.
As such, it is of not much further interest \emph{inside} this section since its behavior can not be derived from the routing table.
The rest of the section is going to continue with the four remaining types.
They can be formalized in the following ways:
\<close>
lemma "rpf_strict rtbl p \<equiv> case routing_table_semantics rtbl (p_src p) of
  Some ra \<Rightarrow> output_iface ra = p_iiface p | 
  None \<Rightarrow> False" using rpf_strict_def .
lemma "rpf_feasible rtbl p \<equiv> \<exists>rr \<in> set rtbl.
  prefix_match_semantics (routing_match rr) (p_src p) \<and> routing_oiface rr = p_iiface p"
  using rpf_feasible_def .
lemma "rpf_loose rtbl p \<equiv> \<exists>rr \<in> set rtbl. prefix_match_semantics (routing_match rr) (p_src p)"
  using rpf_loose_def .
lemma "rpf_loose_ign_default rtbl p \<equiv> \<exists>rr \<in> set rtbl. 
  prefix_match_semantics (routing_match rr) (p_src p) \<and> routing_match rr \<noteq> PrefixMatch 0 0"
  using rpf_loose_ign_default_def .

text\<open>At this point, one might ask whether the above 4 definitions are all sensible ways
  to derive a decision for the source address from the routing table.
  As RFC 3704 already answers this question negatively, here is an example of how one might formalize another level.\<close>
lemma "rpf_semifeasible rtbl p \<equiv> \<exists>rr \<in> set rtbl. 
   prefix_match_semantics (routing_match rr) (p_src p) \<and> routing_oiface rr = p_iiface p
\<and> (\<forall>ra \<in> set rtbl. routing_prefix ra > routing_prefix rr \<longrightarrow>  \<not>prefix_match_semantics (routing_match ra) (p_src p))"
  using rpf_semifeasible_def .
text\<open>This definition is in the middle of strict and feasible RPF:
It allows alternate routes, but only if the alternate routes have the same prefix length.
(This might be useful when using a routing table that has been obtained from a routing protocol
before doing link aggregation\todo{what can I cite?}. However, the reason we show it is its apparent similarity to
@{const longest_prefix_routing}.)
The general answer is (we did not verify this) that there is an infinite amount of possible definitions for RPF based on routing tables
(and these can actually be put into an infinite hierarchy).
We will thus not indulge in any further definitions of RPFs and concentrate on the ones we have.
\<close>
subsection\<open>A hierarchy\<close>
text\<open>One interesting question is whether those definitions stand in any proper relation to each other.
This question is positively answered for all but @{const rpf_loose_ign_default} by Figure \ref{fig:rpfhierar}.
If there is an implication between two of the definitions,
packets that are accepted by the antecedent are also accepted by the succedent.
(All implications have been verified, but they are of the form @{thm rpf_feasible_loose[no_vars]} 
and we decided not to state them all explicitly.
The only exception is the implication from @{const rpf_strict} to @{const rpf_semifeasible},
which also requires three of the routing table validity criteria: @{thm rpf_strict_semifeasible[no_vars]}.
\<close>
text_raw\<open>
\begin{figure}
\centering
\begin{tikzpicture}[
  dli/.style={
    %->,
    %postaction={overlay,double,draw,thick}
    -implies,
    double equal sign distance
  }
]
\node (s) {@{const rpf_strict}};
\node[below=of s] (sf) {@{const rpf_semifeasible}};
\node[below=of sf] (f) {@{const rpf_feasible}};
\node[below=of f] (l) {@{const rpf_loose}};
\node[right=of l] (lid) {@{const rpf_loose_ign_default}};
\draw[dli] (s) -- (sf);
\draw[dli] (sf) -- (f);
\draw[dli] (f) -- (l);
\draw[dli] (lid) -- (l);
\draw[dli,dashed] (lid) edge[bend right=20,->] (s);
\draw[dli,dashed] (l) edge[bend left=50,->] (lid);
\end{tikzpicture}
\caption{The hierarchy of RPF implementations.}
The dashed implications depend on the routing table.
\label{fig:rpfhierar}
\end{figure}
\<close>
text\<open>Interestingly, it is possible to find routing tables that fulfil all validity criteria%
\footnote{@{thm all_valid_rtbl_def[no_vars]}} and make @{const rpf_loose_ign_default} deny any packet, 
while @{const rpf_strict} still accepts some packets (the trick is to only have default routes).
On the other hand side, it is also possible to find routing tables
that make @{const rpf_loose} and @{const rpf_loose_ign_default} behave completely equal
(the trick is to shadow any default rule completely).\<close>
lemma 
  "\<exists>rtbl. all_valid_rtbl rtbl \<and> (\<forall>p. \<not>rpf_loose_ign_default rtbl p) \<and> (\<exists>p. rpf_strict rtbl p)"
  "\<exists>rtbl :: 32 prefix_routing. all_valid_rtbl rtbl \<and> (\<forall>p. rpf_loose rtbl p \<longleftrightarrow> rpf_loose_ign_default rtbl p)"
  using ign_default_mean1 ign_default_mean2 by blast+

subsection\<open>Obtaining IP assignments\<close>
text\<open>Having learned all these things, it is time to answer the central question of this section:
Can appropriate (source) IP assignments be derived from routing tables for all the different RPF types?
For string RPF, this question is immediately answered by @{const routing_ipassmt_wi} from Section \ref{sec:routing_ipass} – the assignment is fully equal.
For all other types, special definitions are necessary, and the two variants of loose RPF need an additional list of possible source interfaces.
Since the actual definitions are not very insightful, we have collected them in @{const rpf_wi_lookup} and just show the following:
\<close>
theorem "\<lbrakk>valid_prefixes rtbl; rpf_type \<in> {RPF_Loose, RPF_LooseIgnDef} \<Longrightarrow> p_iiface p \<in> set ifs\<rbrakk>
\<Longrightarrow> rpf_def_lookup rpf_type rtbl p = (\<exists>(k, l)\<in>set (rpf_wi_lookup rpf_type ifs rtbl). 
  p_iiface p = k \<and> p_src p \<in> wordinterval_to_set l)" using rpf_ipassms .
text\<open>where\<close>
lemma "rpf_def_lookup rpf_type \<in> {rpf_strict, rpf_feasible, rpf_loose, rpf_loose_ign_default, rpf_semifeasible}"
  by(rule rpf_type.exhaust[of rpf_type]; simp) (* interesting way to do a case distinction *)

text\<open>Finally, it is time to evaluate whether all the definitions we have made here are worth anything. 
The first thing that should strike us is the fact that one of the validity criteria we requested of a routing table 
is that it contains a default route.
If we require that and test @{const rpf_loose}, we immediately see that it accepts all packets.\<close>
lemma "valid_prefixes rtbl \<Longrightarrow> has_default_route rtbl \<Longrightarrow> \<forall>p. rpf_loose rtbl p"
  using default_loose_all .
text\<open>
The RFC 3704 authors must have realized this and authored the following paragraph:
\begin{quote}
  The questionable benefit of Loose RPF is found in asymmetric routing
   situations: a packet is dropped if there is no route at all, such as
   to "Martian addresses" or addresses that are not currently routed,
   but is not dropped if a route exists.
\end{quote}
These aspects have fallen prey to our model of routing,
degrading loose RPF from having a ``questionable benefit'' to being entirely useless.
\<close>
text\<open>Furthermore, we know from testing experience that
we want at least an entry for the loopback interface in any source IP assignment.
Unfortunately, the routing rule taking care or the local delivery of \texttt{127.0.0.0/8}
is in the \texttt{local} table and will thus not be considered by our model.\<close>

text\<open>In the end, we decided that the theoretical foundation of using RPF
to obtain source IP assignments from routing tables is still a bit too weak
to activate it as an available algorithm in an automated checking tool.
Instead, we deferred to having the user provide a source IP assignment.
In a sense, we will be using Ingress Access Lists.
\<close>


(*<*)
end
(*>*)
