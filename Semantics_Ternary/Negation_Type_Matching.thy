theory Negation_Type_Matching
imports  Negation_Type Matching_Ternary "../Datatype_Selectors" Fixed_Action
begin

section{*Negation Type Matching*}


text{*Transform a @{typ "'a negation_type list"} to a @{typ "'a match_expr"} via conjunction.*}
fun alist_and :: "'a negation_type list \<Rightarrow> 'a match_expr" where
  "alist_and [] = MatchAny" |
  "alist_and ((Pos e)#es) = MatchAnd (Match e) (alist_and es)" |
  "alist_and ((Neg e)#es) = MatchAnd (MatchNot (Match e)) (alist_and es)"


fun negation_type_to_match_expr :: "'a negation_type \<Rightarrow> 'a match_expr" where
  "negation_type_to_match_expr (Pos e) = (Match e)" |
  "negation_type_to_match_expr (Neg e) = (MatchNot (Match e))"
lemma alist_and_negation_type_to_match_expr: "alist_and (n#es) =  MatchAnd (negation_type_to_match_expr n) (alist_and es)"
by(cases n, simp_all)


(*do I need monads?*)
(*TODO ? ?*)
fun negation_type_to_match_expr_f :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a negation_type \<Rightarrow> 'b match_expr" where
  "negation_type_to_match_expr_f f (Pos a) = Match (f a)" |
  "negation_type_to_match_expr_f f (Neg a) = MatchNot (Match (f a))"

lemma alist_and_append: "matches \<gamma> (alist_and (l1 @ l2)) a p \<longleftrightarrow> matches \<gamma>  (MatchAnd (alist_and l1)  (alist_and l2)) a p"
  apply(induction l1)
   apply(simp_all add: bunch_of_lemmata_about_matches)
  apply(rename_tac l l1)
  apply(case_tac l)
   apply(simp_all add: bunch_of_lemmata_about_matches)
  done


fun to_negation_type_nnf :: "'a match_expr \<Rightarrow> 'a negation_type list" where
 "to_negation_type_nnf MatchAny = []" |
 "to_negation_type_nnf (Match a) = [Pos a]" |
 "to_negation_type_nnf (MatchNot (Match a)) = [Neg a]" |
 "to_negation_type_nnf (MatchAnd a b) = (to_negation_type_nnf a) @ (to_negation_type_nnf b)"


lemma "normalized_nnf_match m \<Longrightarrow> matches \<gamma> (alist_and (to_negation_type_nnf m)) a p  = matches \<gamma> m a p"
  apply(induction m rule: to_negation_type_nnf.induct)
  apply(simp_all add: bunch_of_lemmata_about_matches alist_and_append)
  done
  


text{*Isolating the matching semantics*}
fun nt_match_list :: "('a, 'packet) match_tac \<Rightarrow> action \<Rightarrow> 'packet \<Rightarrow> 'a negation_type list \<Rightarrow> bool" where
  "nt_match_list _ _ _ [] = True" |
  "nt_match_list \<gamma> a p ((Pos x)#xs) \<longleftrightarrow> matches \<gamma> (Match x) a p \<and> nt_match_list \<gamma> a p xs" |
  "nt_match_list \<gamma> a p ((Neg x)#xs) \<longleftrightarrow> matches \<gamma> (MatchNot (Match x)) a p \<and> nt_match_list \<gamma> a p xs"

lemma nt_match_list_matches: "nt_match_list \<gamma> a p l \<longleftrightarrow> matches \<gamma> (alist_and l) a p"
  apply(induction l rule: alist_and.induct)
  apply(simp_all)
  apply(case_tac [!] \<gamma>)
  apply(simp_all add: bunch_of_lemmata_about_matches)
done


lemma nt_match_list_simp: "nt_match_list \<gamma> a p ms \<longleftrightarrow> 
      (\<forall>m \<in> set (getPos ms). matches \<gamma> (Match m) a p) \<and> (\<forall>m \<in> set (getNeg ms). matches \<gamma> (MatchNot (Match m)) a p)"
apply(induction \<gamma> a p ms rule: nt_match_list.induct)
apply(simp_all)
by fastforce

lemma matches_alist_and: "matches \<gamma> (alist_and l) a p \<longleftrightarrow> (\<forall>m \<in> set (getPos l). matches \<gamma> (Match m) a p) \<and> (\<forall>m \<in> set (getNeg l). matches \<gamma> (MatchNot (Match m)) a p)"
by (metis (poly_guards_query) nt_match_list_matches nt_match_list_simp)


end