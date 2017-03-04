section\<open>Routing and IP Assignments\<close>
theory Routing_IpAssmt
imports Ipassmt
        "../../Routing/Routing_Table"
begin
context
begin

subsection\<open>Routing IP Assignment\<close>
text\<open>Up to now, the definitions were all still on word intervals because those are much more convenient to work with.\<close>

definition routing_ipassmt :: "'i::len routing_rule list \<Rightarrow> iface list \<Rightarrow> (iface \<times> ('i word \<times> nat) list) list"
  where
  "routing_ipassmt rt ifs \<equiv> map (apfst Iface \<circ> apsnd cidr_split) (routing_ipassmt_wi rt (map iface_sel ifs))"

private lemma ipcidr_union_cidr_split[simp]: "ipcidr_union_set (set (cidr_split x)) = wordinterval_to_set x" 
  apply(subst cidr_split_prefix[symmetric])
  apply(fact ipcidr_union_set_uncurry)
done

private lemma map_of_map_Iface: "map_of (map (\<lambda>x. (Iface (fst x), f (snd x))) xs) (Iface ifce) = 
        map_option f ((map_of xs) ifce)"
  by (induct xs) (auto)

(*
We used to do trickery like this
lemma "routing_ipassmt_wi ([]::32 prefix_routing) [] = [(output_iface (routing_action (undefined :: 32 routing_rule)), WordInterval 0 0xFFFFFFFF)]"
  by code_simp
to get around having to assume a default route all the time. No more.
*)
lemma "routing_ipassmt_wi ([]::32 prefix_routing) [] = []" by eval


lemma routing_ipassmt: "
    valid_prefixes rt \<Longrightarrow>
    routing_table_semantics rt (p_dst p) = Some ra \<Longrightarrow>
    output_iface ra = p_oiface p \<Longrightarrow>
    \<exists>p_ips. map_of (routing_ipassmt rt ifs) (Iface (p_oiface p)) = Some p_ips \<and> p_dst p \<in> ipcidr_union_set (set p_ips)"
  apply(simp add: routing_ipassmt_def)
  apply(drule routing_ipassmt_wi[where output_port="p_oiface p" and k="p_dst p" and ifs="map iface_sel ifs"])
  apply(simp)
  apply(elim exE, rename_tac ip_range)
  apply(rule_tac x="cidr_split ip_range" in exI)
  apply(simp)
  apply(simp add: comp_def)
  apply(simp add: map_of_map_Iface)
  apply(rule_tac x="ip_range" in exI)
  apply(simp add: routing_ipassmt_wi_distinct)
done

lemma routing_ipassmt_ipassmt_sanity_disjoint: "valid_prefixes (rt::('i::len) prefix_routing) \<Longrightarrow>
    ipassmt_sanity_disjoint (map_of (routing_ipassmt rt ifs))"
unfolding ipassmt_sanity_disjoint_def routing_ipassmt_def comp_def
  apply(clarsimp)
  apply(drule map_of_SomeD)+
  apply(clarsimp split: iface.splits)
using routing_ipassmt_wi_disjoint[where 'i = 'i] by meson

lemma routing_ipassmt_distinct: "distinct (map fst (routing_ipassmt rtbl ifs))"
  using routing_ipassmt_wi_distinct[of rtbl]
  unfolding routing_ipassmt_def
  apply(simp add: comp_def)
  apply(subst distinct_map[where f = Iface and xs = "map fst (routing_ipassmt_wi rtbl (map iface_sel ifs))", simplified, unfolded comp_def])
  apply(auto intro: inj_onI)
done

term ipassmt_sanity_nowildcards
definition "routingtbl_sanity_nowildcards \<equiv> list_all (Not \<circ> iface_is_wildcard \<circ> Iface \<circ> routing_oiface)"
lemma routingtbl_sanity_nowildcards_alt: "routingtbl_sanity_nowildcards rtbl \<longleftrightarrow> (\<forall>rr \<in> set rtbl. \<not>iface_is_wildcard (Iface (routing_oiface rr)))"
  unfolding routingtbl_sanity_nowildcards_def by(simp add: comp_def list_all_iff)
lemma routingtbl_sanity_nowildcards: "\<lbrakk>routingtbl_sanity_nowildcards rtbl; \<forall> iface \<in> set ifs. \<not> iface_is_wildcard iface\<rbrakk>
\<Longrightarrow> ipassmt_sanity_nowildcards (map_of (routing_ipassmt rtbl ifs))"
  unfolding routingtbl_sanity_nowildcards_alt ipassmt_sanity_nowildcards_def
  unfolding routing_ipassmt_def 
  by(auto 
      simp add: comp_def reduce_range_destination_def 
      dest!: map_of_SomeD routing_ipassmt_wi_iface_sources)

  
  
end

end
