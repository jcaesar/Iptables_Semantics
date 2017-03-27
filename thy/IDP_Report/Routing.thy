(*<*)
theory Routing
imports "../Routing/Routing_Table"
begin
(*>*)


section\<open>Routing\<close>
text_raw\<open>\label{sec:routing}\<close>
text\<open>This section shows our formalization of longest prefix routing.
Some of the aspects that are shown here have already been presented in my Bachelor's thesis (or briefly in \cite{LOFT-AFP}).
However, a number of things have been refined, refurbished for a new purpose, or are completely new.
To avoid confusion, this document describes everything comprehensively.\<close>

(* focus on one routing table *)

text\<open>A routing table is formalized as a list of entries:\<close>
lemma "(rtbl :: ('i :: len) prefix_routing) = (rtbl :: 'i routing_rule list)" by rule
text\<open>Each entry in the routing table is then a record of 
\begin{itemize}
  \item a prefix match,
  \item the metric of the route,
  \item an output port, and
  \item an optional next hop IP address.
\end{itemize}
\<close>
schematic_goal "(?rtbl_entry :: ('i::len) routing_rule) = \<lparr> routing_match = PrefixMatch pfx len, metric = met, routing_action = \<lparr> output_iface = oif_string, next_hop = (h :: 'i word option) \<rparr> \<rparr>" ..
text\<open>Note how all types that somehow include an IP address are parametrized with @{typ "'i::len"}. 
This is used to be able to use a single implementation for IPv4 and IPv6.
Depending on the IP protocol that is used, @{typ "'i"} is set to the length of the IP address in bits, @{typ 32} or @{typ 128} respectively.\<close>

text\<open>Not all members of the type @{type prefix_routing} are sane routing tables. 
We came up with four different validity criteria.
They are used in the lemmas as necessary, but they are also required by many of the definitions
in the sense that those definitions simply do not make sense if the criteria are not verified.
The criteria are:
\<close>
text_raw\<open>
\begin{enumerate}
\<close>
text\<open>
  \item
   The prefixes have to be valid, i.e., 0 in bits exceeding their length. \\
    Example: \texttt{127.0.0.0/8} is valid, but \texttt{127.0.0.1/31} is not.
\<close>
lemma
  "valid_prefix (PrefixMatch pfx len) \<equiv> pfx && (2 ^ (32 - len) - 1) = (0 :: 32 word)" 
  "valid_prefixes rtbl = (\<forall>e\<in>set rtbl. valid_prefix (routing_match e))"  
  by (simp_all add: valid_prefix_def pfxm_mask_def mask_def word_bw_comms valid_prefixes_alt_def)
text\<open>(We show the specialized version for @{typ 32} bit since it is easier to read than the general defintion.)
Note: the definition of @{const valid_prefix} forbids prefixes that set bits to one behind their prefix length, as intended.
However, @{const valid_prefix} does not check if the length of the prefix is set to something too high; e.g.\<close>
lemma "valid_prefix (PrefixMatch (0 :: 32 word) 48)" by eval
text\<open>still verifies.
It turns out that these bogus but accepted prefixes are not a hindrance for any of our lemmas anywhere.
Since making weaker assumptions is not harmful, we went for this definition because we deemed it more beautiful than others.\<close>
text\<open>
  \item There has to be a default route, i.e. one with a prefix match of length 0.
\<close>
lemma "has_default_route rt \<longleftrightarrow> (\<exists>r \<in> set rt. pfxm_length (routing_match r) = 0)" 
  by(fact has_default_route_alt)
text\<open>
    With @{const valid_prefixes}, this implies that all its prefix bits are zero and it thus matches any address.\\
    Such a criterion is necessary because our model assumes that the routing table fully makes the forwarding decision.
    Requiring a default route is an easy way to express that this is the case for all packets.
\<close>
text\<open>
  \item \label{crit:rtblsort} The entries have to be sorted by prefix length and metric. 
  We elude the full definition of criterion \ref{crit:rtblsort} since it only asks 
  if the routing table is @{const sorted} lexicographically on prefix length and metric, i.e. by the following key:\<close>
lemma "routing_rule_sort_key r \<equiv> LinordHelper (- int (routing_prefix r)) (metric r)"
 by(simp add: routing_rule_sort_key_def)
text\<open>
  We used a construct called @{const LinordHelper} to build a lexicographic ordering from prefix length and metric.
  We use this since we can not introduce a linear (total) order on routing table entries that correctly represents the order we want
  (because that linear order would have to consider all fields, i.e. also the action part, and thus deem some routes with equal prefix and metric unequal).
\<close>
text\<open>
  \item The sort order has to be unique.
\<close>
lemma "unambiguous_routing rtbl \<longleftrightarrow> (\<forall>rt1 rt2 rr ra. 
  (rtbl = rt1 @ rr # rt2 \<and> ra \<in> set (rt1 @ rt2) \<and> routing_match rr = routing_match ra) \<longrightarrow>
  routing_rule_sort_key rr \<noteq> routing_rule_sort_key ra)" 
  unfolding unambiguous_routing_def by blast
text_raw\<open>
\end{enumerate}
\<close>

text\<open>
\<close>

text\<open>Equipped with these definitions, we can define the ``semantics of a routing table'',
i.e., the evaluation behavior of a packet w.r.t. a routing table.\<close>

text\<open>If you would open a text book on networking, you might find a definition like 
``the routing rule with the most specific match is chosen'', or ``the routing rule with longest matching prefix is used''.
The way to express ``longest matching'' formally is to say that the rule itself matches, and all longer ones do not:\<close>

(* Describe prefix_match_semantics? *)
definition "longest_prefix_routing rtbl addr act \<equiv>
(\<exists>rr \<in> set rtbl. 
  prefix_match_semantics (routing_match rr) addr \<and> 
  routing_action rr = act \<and>
  (\<forall>ra \<in> set rtbl. 
    routing_rule_sort_key ra < routing_rule_sort_key rr \<longrightarrow> 
    \<not>prefix_match_semantics (routing_match ra) addr))"
text\<open>(We use @{const routing_rule_sort_key} to consider the metric in case of matching lengths.)
Note that this is a predicate formulation:
it decides for a given routing rule (or rather: action part of a routing rule, called @{value act} here), 
whether that rule is selected from a routing table given a destination address.
Multiple routes could be selected if @{const unambiguous_routing} is not given.
\<close>
text\<open>Going from this definition directly to a function from routing table and destination address to a routing action
would require using the @{const the}-operator. While doing so is possible,
it would be quite impractical for the derived definitions.
Instead, it is better to sort the routing table and walk over it recursively:
\<close>

lemma
"routing_table_semantics [] p = None"
"routing_table_semantics (r#rs) p = (
    if prefix_match_semantics (routing_match r) p 
    then Some (routing_action r)
    else routing_table_semantics rs p)"
  by simp_all

text\<open>Indeed, these two definitions are equal:\<close>
theorem 
  assumes "valid_prefixes rtbl" and "is_longest_prefix_routing rtbl" and "unambiguous_routing rtbl"
  shows "routing_table_semantics rtbl addr = Some act \<longleftrightarrow> longest_prefix_routing rtbl addr act"
  unfolding longest_prefix_routing_def using assms  by(fact existential_routing)

text\<open>As a last note, we want to mention that if a default route is present, the @{const "routing_table_semantics"} will always produce a result and not return @{const None}.\<close>
lemma "\<lbrakk>valid_prefixes rtbl; has_default_route rtbl\<rbrakk> \<Longrightarrow> routing_table_semantics rtbl p \<noteq> None"
  by (simp add: has_default_route_Some)

subsection\<open>Comparison to a real routing table\<close>
text_raw\<open>\label{sec:realrouting}\<close>
text\<open>This section will compare the model behind @{type prefix_routing} with a real routing table.\<close>
text\<open>If we use the \texttt{ip route}~\cite{maniproute}: command to inspect the routing table on a real linux system,
a typical entry looks like
\begin{align*}
  \text{\texttt{10.0.2.0/24 dev eth0  proto kernel  scope link  src 10.0.1.42}}
\end{align*}
The differences to our model are apparent:
\begin{itemize}
  \item This route has a \texttt{proto} entry that records:
    based on which routing protocol the route was added.
    Obviously irrelevant for our usecase.
  \item This route has a \texttt{scope} entry that records 
    ``the scope of the destinations covered by the route prefix'' \cite{maniproute}.
    The scope does not influence the forwarding decision and is thus irrelevant for us.
  \item This route has a source address hint.
    This hint is used to select a source address for an outgoing packet,
    e.g. when traffic originates from the router itself.
    Since we're interested in the routing table for its description of forwarding,
    abstracting this is obvious. \cite[\paragraphsign 4.6]{brown2007guide}
\end{itemize}
We think that this demonstrates that our abstraction of routing tables has destroyed no important information.
Unfortunately, that only holds true when looking at a single routing table.
\<close>
text\<open>Linux supports having multiple routing tables%
\footnote{They can be viewed with \texttt{ip rule}, %
a single table can be inspected with \texttt{ip route show table [name]}}.
By default, there are three routing tables \texttt{local}, \texttt{main} and, \texttt{default}.
The \texttt{local} is responsible for broadcast traffic and local/loopback delivery,
and the \texttt{default} table is usually empty.
Thus, all the important information for unicast packet forwarding is in the \texttt{main} table
and it is somewhat safe to assume that the system we analyze only has one routing table.
However, this leaves it to the user to check whether the ``one routing table'' assumption is actually correct.
If it does not hold, using information from just one of the routing tables may actually yield incorrect results.
\<close>
text\<open>The choice for this is driven by the need to reduce the complexity of the analysis.
Similar reasoning has been explained and applied to many of the choices in \cite{LOFT-AFP}.
In short, the reason here is that routing table selection in linux is done with an entire separate matching language.
Moreover, the matches can draw upon information from matches in previous matches in the \texttt{mangle} table of IPtables.
On top of that, packets may traverse multiple routing tables before an action is decided.
In sum, this brings it far out of scope of this project to implement an analysis of the routing system that takes all this into consideration and extracts some kind of usable information 
— The cost is far greater than the benefit.
\<close>
text\<open>Henceforth, we will assume that the information of a single routing table is responsible for forwarding decisions.\<close>

subsection\<open>Transformation to a relation\<close>
text_raw\<open>\label{sec:routing_ipass}\<close>
text\<open>This section is going to reinterpret the definitions from the beginning of Section \ref{sec:routing}.\<close>
text\<open>Firstly, if we are interested in routing because it is another function of a firewalling device,
we have no interest in the next hop IP address%
\footnote{The next hop is still part of the model since that is also used by \cite{LOFT-AFP}, which does have an interest in the next hop.}.\<close>
text\<open>Applying that, routing can be seen as
a function or relation from destination IP address to output port (parametrized with the routing table).
If we invert this relation, we get a relation that can be represented by a function from output port to
a set of destination IP addresses that is forwarded via that output port.
We will call such a relation an IP\ assignment (@{value ipassmt}) from here on.
Looking at this from a different angle, we can see a biimplication:
given a pair @{value "(port,ipset)"} from an IP assignment,
a packet is forwarded via @{value "port"} iff its destination IP address is in @{value "ipset"}.
This knowledge will come in handy when transforming firewall rulesets in Section \ref{sec:irew}.
\<close>

text\<open>The question that remains is: can we obtain and represent an IP assignment efficiently?
This is immediately answered by the following simple algorithm:\<close>
lemma
"routing_port_ranges [] lo = []" 
"routing_port_ranges (a#as) lo = (
	let m = prefix_to_wordinterval (routing_match a) in (
	(routing_oiface a,wordinterval_intersection lo m) #
	routing_port_ranges as (wordinterval_setminus lo m)))"
	by (simp_all add: Let_def range_prefix_match_def)
text\<open>The routing table is walked over recursively, 
carrying around a set of IP addresses that did not apply to previous rules
(i.e., rules with longer prefixes or lower metrics).
(Internally, all these sets of IP addresses are represented efficiently by unions of intervals.
The interested reader is referred to study~\cite{IP_Addresses-AFP}.)
For each routing rule, the algorithm emits the rule's output port and the set of IP addresses that match it, under consideration of previous matches.
\<close>
text\<open>For the sake of simplicity, @{const routing_port_ranges} emits one entry per routing rule.
Ensuring that each port only occurs once is done in posterior, in the definition of: @{const routing_ipassmt_wi}:
\<close>
lemma "distinct (map fst (routing_ipassmt_wi rtbl ifs))" by(fact routing_ipassmt_wi_distinct)
text\<open>The definition @{const routing_ipassmt_wi} simply takes the list returned by @{const routing_port_ranges},
 and, for each unique port, constructs the union of all sets that are forwarded to that port.
\<close>text\<open>
In addition, @{const routing_ipassmt_wi} takes a list of interfaces (@{value ifs}).
This is to address the problem that not necessarily every interface that is present on the machine has an entry in the routing table.
If there is an interface without any entry in the routing table routing packets via it,
no packets will ever be routed (forwarded) via that interface\footnote{At least, according to our model of routing.}
and the result of @{const routing_ipassmt_wi} should contain a pair of port and an empty set.
Without the list of interfaces, this information could not be represented.%
\footnote{Surprisingly, introducing the interface did not require a single new case distinction in our proofs.}
See Section~\ref{sec:evalm} for an example of a configuration where this is important.
\<close>

text\<open>Furthermore, the definition of @{const routing_ipassmt_wi} validates the following two interesting lemmas:\<close>

lemma
assumes "valid_prefixes (tbl::('i::len) prefix_routing)"
  and "a1 \<noteq> a2"
  and "(a1, b1) \<in> set (routing_ipassmt_wi tbl ifs)" 
  and "(a2, b2) \<in> set (routing_ipassmt_wi tbl ifs)"
shows "wordinterval_to_set b1 \<inter> wordinterval_to_set b2 = {}"
    -- "the IP assignment properly represents a relation"
using assms by(fact routing_ipassmt_wi_disjoint)
    
theorem
assumes vpfx: "valid_prefixes tbl"
shows "
(\<exists>ra. routing_table_semantics tbl k = Some ra \<and> output_iface ra = output_port) \<longleftrightarrow>
(\<exists>ip_range. k \<in> wordinterval_to_set ip_range \<and> (output_port, ip_range) \<in> set (routing_ipassmt_wi tbl ifs))"
  -- "the IP assignment is in a proper relation with the routing table semantics"
by(intro assms routing_ipassmt_wi)

(* TODO: efficient representation *)

(*<*)
end
(*>*)
