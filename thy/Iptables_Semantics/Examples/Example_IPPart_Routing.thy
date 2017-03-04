theory Example_IPPart_Routing
imports 
  "../Primitive_Matchers/Parser"
begin
  
definition "sanities fw rtbl \<equiv> 
  correct_routing rtbl \<and> has_default_route rtbl \<and> routingtbl_sanity_nowildcards rtbl \<and>
  simple_ruleset fw \<and> simple_ruleset (packet_assume_new fw)"
definition "mtx assmt rtblo fw \<equiv> let m = access_matrix_pretty_ipv4 parts_connection_http
  (to_simple_firewall_without_interfaces assmt rtblo (packet_assume_new fw));
  f = the \<circ> map_of (fst m) in
  map (map_prod f f) (snd m)"
  
(* A truly minimal, but not very meaningful, example: *)
definition "rtbl1 \<equiv> [\<lparr>
  routing_match = PrefixMatch 0 0, 
  metric = 0, 
  routing_action = \<lparr>output_iface = ''eth1'', next_hop = None\<rparr>\<rparr>] :: 32 prefix_routing"

definition "fw1 \<equiv> [
Rule (Match (OIface (Iface ''eth0''))) action.Accept,
Rule MatchAny action.Drop
] :: 32 common_primitive rule list"

lemma "sanities fw1 rtbl1" by eval

value ipassmt_generic_ipv4
lemma "mtx ipassmt_generic_ipv4 None fw1 = [(''{0.0.0.0 .. 255.255.255.255}'', ''{0.0.0.0 .. 255.255.255.255}'')]" by eval
lemma "mtx ipassmt_generic_ipv4 (Some rtbl1) fw1 = []" by eval

(* a maybe slightly more meaningful example: *)
definition "assmt2 \<equiv> let private = ipv4addr_of_dotdecimal (10,0,1,0);
  nonprivate = wordinterval_setminus wordinterval_UNIV (ipcidr_tuple_to_wordinterval (private,24)) in [
  (Iface ''eth1'', [(private, 24)]),
  (Iface ''eth2'', cidr_split nonprivate)
]" (* I'll skip lo. *)
definition "rtbl2 \<equiv> [
	rr_ctor (10,0,1,0) 24 ''eth1'' None 0,
	rr_ctor (10,0,2,0) 24 ''eth2'' None 0,
	rr_ctor (0,0,0,0) 0 ''eth2'' (Some (10,0,2,1)) 0
] :: 32 prefix_routing"

definition "MatchAND L \<equiv> foldr (MatchAnd \<circ> Match) L MatchAny"
definition "fw2 \<equiv> [
Rule (Match (CT_State {CT_Related,CT_Established})) action.Accept,
Rule (MatchAND [
  CT_State {CT_New,CT_Established,CT_Related}, 
  IIface (Iface ''eth1''), OIface (Iface ''eth2'')]) action.Accept,
Rule MatchAny action.Drop
] :: 32 common_primitive rule list"

value[code] "to_simple_firewall (packet_assume_new fw2)"
lemma "sanities fw2 rtbl2" by eval
value "mtx assmt2 None fw2"
lemma "mtx [] None fw2 = [
  (''{0.0.0.0 .. 255.255.255.255}'', ''{0.0.0.0 .. 255.255.255.255}'')]" 
  (* IE: Firewall doesn't ensure anything. *) by eval
lemma "mtx assmt2 (Some rtbl2) fw2 = [
  (''{10.0.1.0 .. 10.0.1.255}'', ''{0.0.0.0 .. 10.0.0.255} u {10.0.2.0 .. 255.255.255.255}'')]" by eval
(* Note that we already get relatively interesting results when only providing a source assignment: *)
lemma "mtx assmt2 None fw2 = [
  (''{10.0.1.0 .. 10.0.1.255}'', ''{10.0.1.0 .. 10.0.1.255}''),
  (''{10.0.1.0 .. 10.0.1.255}'', ''{0.0.0.0 .. 10.0.0.255} u {10.0.2.0 .. 255.255.255.255}'')]"
  by eval



end