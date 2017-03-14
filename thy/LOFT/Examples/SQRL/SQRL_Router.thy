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
  m = \<lambda>(i,b,c,d,e,f). (Iface i, [(a (b,c,d,e), f)])
  in [
  m (''ldit'', 10,13,42,136,29),
  m (''lmd'', 10,13,42,128,29),
  m (''loben'', 10,13,42,144,28),
  m (''wt'', 10,13,42,160,28),
  m (''wg'', 10,13,41,0,27),
  (Iface ''lup'', all_but_those_ips [(a (192,168,0,0),16), (a (10,0,0,0),8), (a (127,16,0,0),12)]),
  (Iface ''vpriv'', [(a (10,13,44,0),24), (a (10,13,37,0),24)]),
  m (''vshit'', 10,13,43,0,28),
  m (''vocb'', 10,13,43,16,28),
  m (''zonespanning'', 0,0,0,0,0),
  (Iface ''lua'', [])
] :: (iface \<times> (32 word \<times> nat) list) list"
(* okay, I'm hacking around a bit here. Interface zonespanning obviously doesn't exist,
   but it will cause the rewriter to think that there are zonespanning interfaces and that it needs
   to preserve input interfaces. Which I want for a nicer openflow ruleset. *)

term SQRL_fw
thm SQRL_fw_def
thm SQRL_fw_FORWARD_default_policy_def
value ipassmt
find_theorems odd
typ "32 word"

value[code] "map (\<lambda>(c,rs). (c, map (quote_rewrite \<circ> common_primitive_rule_toString) rs)) SQRL_fw"
definition "unfolded = unfold_ruleset_FORWARD SQRL_fw_FORWARD_default_policy (map_of_string_ipv4 SQRL_fw)"
definition "sanitized assmt rtblo st \<equiv> 
  (upper_closure (optimize_matches abstract_for_simple_firewall (*(abstract_primitive 
    (\<lambda>r. case r of Pos a \<Rightarrow> is_L4_Flags a | Neg a \<Rightarrow> is_L4_Flags a))*)
  (upper_closure (iface_try_rewrite assmt rtblo
  (upper_closure (st unfolded))))))"

lemma "length unfolded = 69" by eval

value[code] "unfolded"
value[code] "(upper_closure unfolded)"
value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (upper_closure unfolded)"
lemma "length (upper_closure unfolded) = 69" by eval


value[code] "upper_closure (packet_assume_new unfolded)"
  
lemma "length (lower_closure unfolded) = 55" by eval

(* say we'd happen to forget to abstract for simple_fw / remove the l4 matches *)
value[code] "report_simple_fw_preconditions (upper_closure (packet_assume_new unfolded))"

lemma "check_simple_fw_preconditions (sanitized ipassmt None packet_assume_new)" by eval
lemma "check_simple_fw_preconditions (sanitized ipassmt (Some SQRL_rtbl_main) packet_assume_new)" by eval
    
(* quick look at the access matrix (for http): *)
value[code] "let m = access_matrix_pretty_ipv4 parts_connection_http
  (to_simple_firewall_without_interfaces ipassmt (Some SQRL_rtbl_main) 
    unfolded);
  f = the \<circ> map_of (fst m) in
  map (map_prod f f) (snd m)"
(* but that's not what we're here for. *)

  
definition "packet_assume_established \<equiv> optimize_matches (ctstate_assume_state CT_Established)"
definition "SQRL_fw_simple_new \<equiv> remdups_rev (to_simple_firewall (sanitized ipassmt (Some SQRL_rtbl_main) packet_assume_new))"
definition "SQRL_fw_simple_est \<equiv> remdups_rev (to_simple_firewall (sanitized ipassmt (Some SQRL_rtbl_main) packet_assume_established))"
lemma "simple_fw_valid SQRL_fw_simple_new" by eval
lemma "simple_fw_valid SQRL_fw_simple_est" by eval    
lemma "length SQRL_fw_simple_new = 313" by eval
lemma "length SQRL_fw_simple_est = 362" by eval
value[code] "SQRL_fw_simple_new"
value[code] "SQRL_fw_simple_est"
(* fun fact: *)
lemma "no_oif_match SQRL_fw_simple_new" by eval
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

definition "ofi fw \<equiv> 
    case (lr_of_tran SQRL_rtbl_main fw (map fst SQRL_ports))
    of (Inr openflow_rules) \<Rightarrow> map (serialize_of_entry (the \<circ> map_of SQRL_ports)) openflow_rules"
lemma "length (ofi SQRL_fw_simple_new) = 365" by eval
lemma "length (ofi SQRL_fw_simple_est) = 773" by eval
value[code] ofi


ML\<open>
let
fun mgck term file = let
	val evterm = the (Code_Evaluation.dynamic_value @{context} term);
	val opstr = map (fn s => HOLogic.dest_string s ^ "\n") (HOLogic.dest_list evterm)
in
	File.write_list (Path.explode (File.platform_path(Resources.master_directory @{theory}) ^ "/" ^ file)) opstr
end
in
(mgck @{term "ofi SQRL_fw_simple_new"} "sqrl_of_new.txt", 
 mgck @{term "ofi SQRL_fw_simple_est"} "sqrl_of_est.txt")
end
\<close>

end