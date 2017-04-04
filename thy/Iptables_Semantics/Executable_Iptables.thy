section\<open>Example: Executing an Iptables ruleset in Isabelle\<close>
theory Executable_Iptables
  imports Alternative_Semantics "Primitive_Matchers/Common_Primitive_Matcher" 
    (* arbitrarily: *) "Examples/SQRL_Shorewall/SQRL_2015_nospoof"
begin
text\<open>This is just a little example theory that demonstrates that one can directly
  execute a loaded ruleset with an inductively defined semantics.
  This makes for an interesting toy example.
  We could now export this as code and do a large-scale traffic evaluation to see if our model and semantics
  do actually match the real implementation\<close>
(* Generating code for predicates is black magic.
  Since I don't really have an application for this right now,
  I don't see much to gain from messing with it any further. *)

code_pred (modes: i => i => i => i => o => bool as compute_iptables_bigstep_r,
    i => i => i => i => i => bool) iptables_bigstep_r .
(* print_theorems *)
    
definition "some_p \<equiv> \<lparr>p_iiface = ''lmd'', p_oiface = ''lup'',
           p_src = ipv4addr_of_dotdecimal (10,13,42,130), p_dst= ipv4addr_of_dotdecimal (80,237,132,143),
           p_proto=TCP, p_sport=51065, p_dport=80, p_tcp_flags = {},
           p_payload = '''', p_tag_ctstate = CT_New\<rparr>"

(*values "{t. (\<lambda>_. None),(\<lambda>m p. the (ternary_to_bool (common_matcher m p))),some_p\<turnstile> \<langle>[],Undecided\<rangle> \<Rightarrow> t}"
  This won't work. I have no idea if one somehow can make it work\<dots> *)
term "map_of_string_ipv4 filter_fw1"
definition "entry_rs \<equiv> [Rule MatchAny (Call ''FORWARD''), Rule MatchAny filter_fw1_FORWARD_default_policy]"
values "{t. (map_of_string_ipv4 filter_fw1),(\<lambda>m p. the (ternary_to_bool (common_matcher m p))),some_p \<turnstile>
  entry_rs \<Rightarrow>\<^sub>r t}"
lemma "(map_of_string_ipv4 filter_fw1),(\<lambda>m p. the (ternary_to_bool (common_matcher m p))),some_p
  \<turnstile> entry_rs \<Rightarrow>\<^sub>r Decision FinalAllow" by eval
lemma "Predicate.the (compute_iptables_bigstep_r 
  (map_of_string_ipv4 filter_fw1) (\<lambda>m p. the (ternary_to_bool (common_matcher m p))) some_p entry_rs) = 
  Decision FinalAllow" by eval

export_code compute_iptables_bigstep_r checking Haskell
  

end