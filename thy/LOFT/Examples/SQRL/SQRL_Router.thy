theory SQRL_Router
  imports
    "../../../Iptables_Semantics/Primitive_Matchers/Parser"
    "../../../Routing/IpRoute_Parser"
    "../../LinuxRouter_OpenFlow_Translation"
    "../../OpenFlow_Serialize"
begin
  
parse_iptables_save SQRL_fw="iptables-save"
parse_ip_route SQRL_rtbl_main = "ip-route"
definition "ipassmt \<equiv> let
  a = ipv4addr_of_dotdecimal;
  i = \<lambda>(b,c,d,e,f). ipcidr_tuple_to_wordinterval (a (b,c,d,e), f);
  m = \<lambda>(i,b,c,d,e,f::nat). (Iface i, [(a (b,c,d,e), f)])
  in [
  m (''ldit'', 10,13,42,136,29),
  m (''lmd'', 10,13,42,128,29),
  m (''loben'', 10,13,42,144,28),
  (Iface ''lup'', cidr_split (wordinterval_setminus wordinterval_UNIV
    (wordinterval_Union [i (192,168,0,0,16), i (10,0,0,0,8), i (127,16,0,0,12)]))),
  m (''vocb'', 10,13,43,16,28),
 (Iface ''vpriv'', [(a (10,13,44,0),24), (a (10,13,37,0),24)]),
  m (''vshit'', 10,13,43,0,28),
  m (''wg'', 10,13,41,0,27),
  m (''wt'', 10,13,42,160,28)
] :: (iface \<times> (32 word \<times> nat) list) list"

term SQRL_fw
thm SQRL_fw_def
thm SQRL_fw_FORWARD_default_policy_def
value ipassmt
find_theorems odd
typ "32 word"

value[code] "map (\<lambda>(c,rs). (c, map (quote_rewrite \<circ> common_primitive_rule_toString) rs)) SQRL_fw"
definition "unfolded = unfold_ruleset_FORWARD SQRL_fw_FORWARD_default_policy (map_of_string_ipv4 SQRL_fw)"
definition "sanitized assmt rtblo \<equiv> 
  (upper_closure (optimize_matches abstract_for_simple_firewall (*(abstract_primitive 
    (\<lambda>r. case r of Pos a \<Rightarrow> is_L4_Flags a | Neg a \<Rightarrow> is_L4_Flags a))*)
  (upper_closure (iface_try_rewrite assmt rtblo
  (upper_closure (packet_assume_new unfolded))))))"

lemma "length unfolded = 69" by eval

value[code] "unfolded"
value[code] "(upper_closure unfolded)"
value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (upper_closure unfolded)"
lemma "length (upper_closure unfolded) = 69" by eval


value[code] "upper_closure (packet_assume_new unfolded)"
  
lemma "length (lower_closure unfolded) = 55" by eval

(* say we'd happen to forget to abstract for simple_fw / remove the l4 matches *)
value[code] "report_simple_fw_preconditions (upper_closure (packet_assume_new unfolded))"

lemma "check_simple_fw_preconditions (sanitized ipassmt None)" by eval
lemma "check_simple_fw_preconditions (sanitized ipassmt (Some SQRL_rtbl_main))" by eval
    
(* quick look at the access matrix (for http): *)
value[code] "let m = access_matrix_pretty_ipv4 parts_connection_http
  (to_simple_firewall_without_interfaces ipassmt (Some SQRL_rtbl_main) 
    unfolded);
  f = the \<circ> map_of (fst m) in
  map (map_prod f f) (snd m)"
(* but that's not what we're here for. *)

  

definition "SQRL_fw_simple \<equiv> remdups_rev (to_simple_firewall (sanitized ipassmt (Some SQRL_rtbl_main)))"
lemma "simple_fw_valid SQRL_fw_simple" by eval
lemma "length SQRL_fw_simple = 618" by eval
value[code] "SQRL_fw_simple"
lemma "simple_fw_valid SQRL_fw_simple" by eval
(* fun fact: *)
lemma "no_oif_match SQRL_fw_simple" by eval
(* I mean, we can abstract over interfaces using
  upper_closure \<circ> optimize_matches (abstract_primitive
  (\<lambda>r. case r of Pos a \<Rightarrow> is_Oiface a | Neg a \<Rightarrow> is_Oiface a))
  The fun part is that we don't have to do that. *)

definition "SQRL_ports \<equiv> [
  (''ldit'', ''1''),
  (''lmd'', ''2''),
  (''loben'', ''3''),
  (''lup'', ''4''),
  (''vocb'', ''5''),
  (''vpriv'', ''6''),
  (''vshit'', ''7''),
  (''wg'', ''8''),
  (''wt'', ''9'')
]"

definition "ofi \<equiv> 
    case (lr_of_tran SQRL_rtbl_main SQRL_fw_simple (map fst SQRL_ports))
    of (Inr openflow_rules) \<Rightarrow> map (serialize_of_entry (the \<circ> map_of SQRL_ports)) openflow_rules"
lemma "length ofi = 606" by eval
value[code] ofi

(* TODO: Well, that's something\<dots> I'd really like to have a proper file with newlines though\<dots> *)
(*ML\<open>
	val evterm = the (Code_Evaluation.dynamic_value @{context} @{term "intersperse (Char Nibble0 NibbleA) ofi"});
	val opstr = Syntax.string_of_term (Config.put show_markup false @{context}) evterm;
	File.write (Path.explode (File.platform_path(Resources.master_directory @{theory}) ^ "/pretty_str.txt")) opstr;
\<close>*)

end
  
