(*<*)
theory InterfaceRewriting
  imports "../Iptables_Semantics/Simple_Firewall/SimpleFw_Compliance"
begin
(*>*)

section\<open>Interface Rewriting\<close>
text_raw\<open>\label{sec:irew}\<close>


text\<open>In Section \ref{sec:routing}, we showed how to derive an efficient representation of an IP assignment,
a relation that describes which sets of IP addresses are expected on a port.
This section will show how to use IP assignments to modify interface match expressions.
The technique has already been briefly introduced with \cite[III D]{diekmann2016verified},
but for ingress interfaces only.
This section will thus give a short superficial overview over the firewall-related formalizations,
for a more in-depth description \cite{diekmann2016verified,Iptables_Semantics-AFP} is recommended.
\<close>

text\<open>The system behind \cite{diekmann2016verified} introduces two types of firewall formalizations.
One is a full-blown model that can represent any Iptables ruleset.
The other one is a simplified model of a firewall that only allows a single list of rules
  that can only accept or drop packets based on matches on interfaces, IP addresses, and layer 4 protocol and ports.
The system behind \cite{diekmann2016verified} simplifies firewalls in multiple steps, e.g. unfolding calls to subchains,
abstracting over unknown match expressions, converting to negation/disjunctive normal form (NNF/DNF) (multiple times), \dots
Rewriting interfaces is implemented as just another of those steps.
\<close>

text\<open>
Before we can start rewriting interfaces in firewall rulesets, we need to fix one thing:
We remained relatively unspecific about how the sets of IP addresses are represented, merely stating that they are intervals.
The ``lingua franca'' of representing sets of IP addresses in firewalls is using prefix matches.
The problem with that is that the sets that are produced by Section \ref{sec:routing} can not always be represented by a single prefix match.
Fortunately, there is a simple greedy algorithm that converts any set of IP addresses to a list of prefix matches.
This algorithm has been presented with \cite{diekmann2016verified} and is implemented in \cite{IP_Addresses-AFP}.
\<close>
text\<open>Thus, we can fix the type of an IP assignment to be:\<close>
type_synonym 'i ipassmt = "(iface \<times> ('i word \<times> nat) list) list"
text\<open>i.e., an @{type ipassmt} is a list of pairs of interfaces and IP address sets,
where the sets are represented by lists of prefix matches.\<close>

text\<open>Now, we can get get to rewriting.
Rewriting is going to happen on firewall rulesets while they are still in the Iptables model
(but after removing all call/return/goto statements, so we will not have to bother with multiple chains).
The reason for this threefold:
\begin{itemize}
  \item It is slightly simpler to do so since the Iptables model supports disjunctions in match expressions (see below).
  \item We already had all the machinery available on those expressions.
  \item The simple firewall does not support negated match expressions like \texttt{! -o eth0}.
    Such expressions will be lost after the conversion to simple firewalls --
    by rewriting those to sets of IP addresses, their information can be preserved.
\end{itemize}
\<close>

text\<open>Thus, we look for any occurence of an interface match (e.g., @{term "Match (OIface ifce)"}) in the firewall.
If the interface name is in the IP assignment%
\footnote{Note that we assume that the IP assignment interface names do not end with a \texttt{+} 
  (@{const ipassmt_sanity_nowildcards}). Thus, wildcard interface matches will be left untouched.}
we can replace it by a disjunction matching the different prefixes that are recorded in the IP assignment.
If the IP assignment does not have anything recorded, the output interface match is kept (and can be abstracted away later).
In code, that looks the following way for output interfaces:
\<close>
lemma
  "ipassmt_iface_replace_dstip_mexpr ipassmt ifce \<equiv> case ipassmt ifce of
     None \<Rightarrow> Match (OIface ifce)
   | Some pfxs \<Rightarrow> (match_list_to_match_expr 
      (map (Match \<circ> Dst) (map (uncurry IpAddrNetmask) pfxs)))"
  unfolding ipassmt_iface_replace_dstip_mexpr_def .
text\<open>The version that replaces input interfaces is \emph{mutatis mutandem}.
However, it can only be used when the user supplied an IP assignment where no IP is assigned to more than one interface
 (as checked by @{const ipassmt_sanity_disjoint}).
If there is an IP that appears on more than one interface, those interface matches would have to be kept
 alongside the source prefix matches.
For simplicity, the algorithm keeps all interface matches in that case, as they can simply be abstracted away later.
\<close>
text\<open>To recursively descend over the match expressions' boolean expression,
 we need the helper function @{const oiface_rewrite}.
We need an additional helper function to map @{const oiface_rewrite} over all match expressions in the rule list.
For this purpose, we use the @{const optimize_matches} function that additionally removes trivially empty matches.
The implementations of these two functions are trivial and relatively uninteresting, however, their use bears a problem:
They only act correctly (and thus are only proven correct) for match expressions that are in disjunctive normal form (DNF).
However, the result they produce is clearly not always in DNF.
Thus, if we want to run the algorithms twice -- once for input and once for output interfaces --
we need to normalize the expressions in between.
This makes the whole rewriting definition look like%
\footnote{@{const routing_ipassmt} is a version of @{const routing_ipassmt_wi}
that corrects the correct type of @{type ipassmt}}:
\<close>
lemma "\<lbrakk>ipassmt_sanity_disjoint (map_of ipassmt) \<and> ipassmt_sanity_defined rs (map_of ipassmt)\<rbrakk>
   \<Longrightarrow> iface_try_rewrite ipassmt (Some rtbl) rs =
    (optimize_matches (iiface_rewrite (map_of_ipassmt ipassmt)) \<circ>
    transform_optimize_dnf_strict \<circ>
    optimize_matches (oiface_rewrite (map_of_ipassmt (routing_ipassmt rtbl
      (filter (Not \<circ> iface_is_wildcard) (collect_ifaces rs))))))
    rs"
  unfolding iface_try_rewrite_def by simp
text\<open>We only show the case where a routing table is available
  (otherwise, the DNF-transformation and output interface rewriting are skipped)
and the provided source IP assignment is sane (otherwise, @{const iiface_constrain} would have been used).
One thing to notice is the @{term "filter (Not \<circ> iface_is_wildcard) (collect_ifaces rs)"} parameter to @{const routing_ipassmt}.
In Section \ref{sec:routing_ipass}, we explained that an Interface might exist on a host but not be in the routing table.
To prevent that we know nothing about interfaces that appear in the firewall but not in the routing table,
 we simply collect all non-wildcard interface matches and use that as a list of interfaces.
While this list might not include all interfaces on the specific host, it includes all the interfaces that are of interest.
\<close>

(*

Read the routing table
produce a relation ip-interval -> port (position independent, reduced intervals)
invert the relation
(proof: strict rpf (RCF3704) corresponds to this)
transform to ipassmt (split intervals)

Fundamental difference: output port rewriting should kill anything that is not in the routing table.
when generating the assignment naively, interfaces with no routing rule receive no entry in the ipassignment.
the interface rewriting will ignore interfaces with no entry, and they will later be abstracted to match all, 
yielding overapproximation.
*)

(* optimize_matches removes matches that accept nothing,
  transform_optimize_dnf_strict transforms to DNF and removes none/any
  the function oiface_rewrite (iiface_rewrite) simply apply 
  the function ipassmt_iface_replace_dstip_mexpr (ipassmt_iface_replace_srcip_mexpr)
  to all the Match-leaves of the match expression that do an OIface (IIface) match.
all others remain unchanged:
 
lemma
  "oiface_rewrite ipassmt (Match (OIface ifce)) = ipassmt_iface_replace_dstip_mexpr ipassmt ifce"
  "(\<And>ifce. a \<noteq> (OIface ifce)) \<Longrightarrow> oiface_rewrite ipassmt (Match a) = Match a"
  "oiface_rewrite ipassmt MatchAny = MatchAny"
  by(force intro: common_primitive.exhaust[of a])+

term optimize_matches
*)
(* reason we're not using collect_ifaces: wildcard interfaces *)

(*<*)
end
(*>*)
