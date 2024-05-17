theory regex
  imports "HOL.Main"
begin

datatype regex =
  Empty |
  Eps |
  Char "bool" |
  Many "regex" |
  Plus "regex" "regex" |
  Concat "regex" "regex"

type_synonym language = "bool list \<Rightarrow> bool"

fun optn_language :: "language \<Rightarrow> language" where
  "optn_language lang lst = (lst = [] \<or> lang lst)"

fun plus_language :: "language \<Rightarrow> language \<Rightarrow> language" where
  "plus_language lang1 lang2 lst =
    ((lang1 lst) \<or> (lang2 lst))"

fun concat_language_helper :: "language \<Rightarrow> language \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool" where
  "concat_language_helper lang1 lang2 prefix []
    = (lang1 prefix \<and> lang2 [])"
| "concat_language_helper lang1 lang2 prefix (x#xs)
    = ((lang1 prefix \<and> lang2 (x#xs)) \<or>
          (concat_language_helper lang1 lang2 (prefix @ [x]) xs))"

fun concat_language :: "language \<Rightarrow> language \<Rightarrow> language" where 
  "concat_language lang1 lang2 lst = 
    concat_language_helper lang1 lang2 [] lst"

fun many_language_helper :: "language \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool" 
  where
  "many_language_helper lang prefix [] = (prefix = [] \<or> lang prefix)" |
  "many_language_helper lang [] (x#xs) = 
    many_language_helper lang [x] xs" | 
  "many_language_helper lang prefix (x#xs) = 
    ((lang prefix \<and> many_language_helper lang [] (x#xs))
      \<or> many_language_helper lang (prefix @ [x])  xs)"


fun many_language :: "language \<Rightarrow> language" where
  "many_language lang lst = many_language_helper lang [] lst"




fun rev_language :: "language \<Rightarrow> language" where
  "rev_language lang lst = lang (rev lst)"



fun regex_language :: "regex \<Rightarrow> language" where
    "regex_language Empty = (\<lambda> l. False)" |
    "regex_language Eps = (\<lambda> l. l = [])" |
    "regex_language (Char n) = (\<lambda> l. l = [n])" | 
    "regex_language (Many r) = many_language (regex_language r)" | 
    "regex_language (Plus r s) = 
      (\<lambda> l. (regex_language r l) \<or> (regex_language s l))" | 
    "regex_language (Concat r s) = 
      concat_language (regex_language r) (regex_language s)"


fun Compl :: "regex \<Rightarrow> regex" where
  "Compl Empty = Empty" |
  "Compl Eps = Eps" |
  "Compl (Char b) = Char (\<not> b)" |
  "Compl (Many r) = Many (Compl r)" |
  "Compl (Plus r s) = Plus (Compl r) (Compl s)" | 
  "Compl (Concat r s) = Concat (Compl r) (Compl s)"


fun Rev :: "regex \<Rightarrow> regex" where
  "Rev Empty = Empty" |
  "Rev Eps = Eps" |
  "Rev (Char n) = Char n" |
  "Rev (Many r) = Many (Rev r)" |
  "Rev (Plus r s) = Plus (Rev r) (Rev s)" | 
  "Rev (Concat r s) = Concat (Rev s) (Rev r)"

fun Optn :: "regex \<Rightarrow> regex" where
  "Optn r = Plus Eps r"

fun c :: "regex \<Rightarrow> regex" where
  "c Empty = Empty" |
  "c Eps = Eps" |
  "c (Char n) = Empty" |
  "c (Many r) = Eps" |
  "c (Plus r s) = Plus (c r) (c s)" | 
  "c (Concat r s) = Concat (c s) (c r)"

lemma Optn_correct : "regex_language (Optn r) l = optn_language (regex_language r) l"
  by simp

lemma Plus_Empty_r : "regex_language (Plus r Empty) l = regex_language r l"
  by simp

lemma Plus_Empty_l : "regex_language (Plus Empty r) l = regex_language r l"
  by simp

lemma Plus_comm : "regex_language (Plus r s) l = regex_language (Plus s r) l"
  by auto

lemma Plus_assoc : "regex_language (Plus r (Plus s t)) l = regex_language (Plus (Plus r s) t) l"
  by auto


fun rev_corr :: "regex \<Rightarrow> bool list \<Rightarrow> bool" where
  "rev_corr r l =
  (regex_language (Rev r) l = rev_language (regex_language r) l)"

fun rev_corr' :: "regex \<Rightarrow> bool" where
  "rev_corr' r = 
  (regex_language (Rev r) = rev_language (regex_language r))"

lemma rev_corr'_eq_forall_rev_corr : 
  "rev_corr' r = (\<forall> l. rev_corr r l)"
  by auto

lemma forall_rev_corr_eq_rev_corr' : 
  "(\<forall> l. rev_corr r l) = rev_corr' r"
  by auto

lemma regex_language_Optn : "regex_language (Optn r) = (\<lambda> l. l = [] \<or> regex_language r l)"
  by simp

lemma rev_Optn : "Rev (Optn r) = Optn (Rev r)"
  by simp

lemma "rev_corr r l \<longrightarrow> rev_corr (Optn r) l"
  by simp


lemma metaspec : "(\<And> x. P x) \<Longrightarrow> P x"
  by simp

lemma concat_helper_iff_ex_app :
  "concat_language_helper lang1 lang2 prefix lst = 
    (\<exists> l1 l2. lst = l1 @ l2 \<and> (lang1 (prefix @ l1)) \<and> lang2 l2)"
  apply (induct lst arbitrary: prefix)
  subgoal by simp
  apply (simp only: concat_language_helper.simps)
  apply (drule meta_spec[of _ prefix])
  apply (erule subst)
  apply (simp; auto)
  subgoal by (rule exI[of _ "[]"]; simp)
  
    apply (rule_tac x="a#l1" in exI; simp)[]
   apply (case_tac "l1"; simp)[]
  apply (case_tac "l1"; simp)
  done

lemma concat_iff_ex_app : 
  "concat_language lang1 lang2 lst = 
    (\<exists> l1 l2. lst = l1 @ l2 \<and> (lang1 (l1)) \<and> lang2 l2)"
  by (simp add: concat_helper_iff_ex_app)

lemma regex_lang_Concat : 
  "regex_language (Concat r s) = concat_language (regex_language r) (regex_language s)"
  by simp

lemma rev_concat_language : 
  "rev_language (concat_language l1 l2) lst = concat_language (rev_language l2) (rev_language l1) lst"
  apply (simp only: concat_iff_ex_app)
  apply (simp only: rev_language.simps concat_iff_ex_app)
  apply (auto)
   apply (rule_tac x="rev l2a" in exI)
   apply (rule_tac x="rev l1a" in exI)
   apply (simp)
   apply (subst (asm) List.rev_swap; erule ssubst; simp)

  apply (rule_tac x="rev l2a" in exI)
  apply (rule_tac x="rev l1a" in exI)
  apply (erule subst; auto)
  done

lemma rev_Concat : "Rev (Concat r s) = Concat (Rev s) (Rev r)"
  by simp

lemma rev_corr_Concat_ind : 
  "(\<forall> l. rev_corr r l) \<Longrightarrow> (\<forall> l. rev_corr s l) 
    \<Longrightarrow> rev_corr (Concat r s) l"
  apply (simp only: rev_corr.simps)
  apply (subst regex_lang_Concat)
  apply (subst rev_Concat)
  apply (subst regex_lang_Concat)
  apply (subst rev_concat_language)
  apply (simp only: concat_iff_ex_app)
  done

lemma rev_corr_Optn_ind:
  "(\<forall> l. rev_corr r l) \<longrightarrow> rev_corr (Optn r) l"
  by simp

lemma many_helper_lst_nil : 
  "many_language_helper lang prefix [] = (prefix = [] \<or> lang prefix)"
  by (simp)
























lemma many_helper_prefix_Cons : 
  "many_language_helper lang prefix (x#xs) = 
    ((lang prefix \<and> many_language_helper lang [] (x#xs))
      \<or> many_language_helper lang (prefix @ [x])  xs)"
  by (case_tac prefix; auto)































lemma many_language_of_lang : 
  "lang (prefix @ lst) \<Longrightarrow> many_language_helper lang prefix lst"
  apply (induction lst arbitrary:prefix)
  subgoal by (simp)
  apply(subst many_helper_prefix_Cons)
  apply (rule disjI2; simp)
  done



lemma many_language_eq_plus_concat :
  "many_language_helper lang prefix lst = 
  (prefix @ lst = [] \<or> (concat_language_helper lang (many_language lang) prefix lst))"
  apply (induction lst arbitrary:prefix; simp)
  apply (subst many_helper_prefix_Cons; simp)
  done

lemma many_helper_iff_ex : 
  "many_language_helper lang prefix lst =
  (prefix @ lst = [] \<or>
  (\<exists> l1 l2. lst = l1 @ l2 \<and> lang (prefix @ l1) \<and> many_language_helper lang [] l2))"
  apply (subst many_language_eq_plus_concat)
  apply (simp add: concat_helper_iff_ex_app)
  done    


lemma many_iff_ex : "many_language lang lst = (lst = [] \<or> (\<exists> l1 l2. lst = l1 @ l2 \<and> lang l1 \<and> many_language lang l2))" 
  (is "?P (many_language lang lst)")
  apply (simp)
  apply (subst many_helper_iff_ex[of "lang" "[]" "lst"])
  by auto

lemma funext : "(\<forall> x. f x = g x) \<Longrightarrow> f = g"
  by auto

lemma rev_plus_language : 
  "rev_language (\<lambda> lst. lang1 lst \<or> lang2 lst) lst = 
   rev_language lang1 lst \<or> rev_language lang2 lst"
  by auto

lemma many_language_Cons_eq_concat : 
  "many_language lang (a#lst) = 
    concat_language (\<lambda> l. lang (a#l)) (many_language lang) lst"
  apply (subst concat_iff_ex_app)
  apply (simp)
  apply (subst many_helper_iff_ex)
  by simp

lemma many_language_app_of_lang_many : 
  "lang lst1 \<Longrightarrow> many_language lang lst2 \<Longrightarrow> 
  many_language lang (lst1 @ lst2)"
  apply (subst many_iff_ex)
  apply (rule disjI2)
  apply (rule exI[of _ lst1])
  apply (rule exI[of _ lst2])
  by auto

lemma many_language_app_of_lang_many_helper :
  "lang lst1 \<Longrightarrow> many_language lang lst2 \<Longrightarrow>
  many_language_helper lang [] (lst1@lst2)"
  apply (insert many_language_app_of_lang_many)
  by auto

inductive concat_ind :: "language \<Rightarrow> language \<Rightarrow> language" where
  concat_conj : 
  "lang1 lst1 \<Longrightarrow> lang2 lst2 \<Longrightarrow> concat_ind lang1 lang2 (lst1@lst2)"

lemma ex2E : "(\<And> x y. P x y \<Longrightarrow> Q) \<Longrightarrow> \<exists> x y. P x y \<Longrightarrow> Q"
  by auto

lemma concat_iff_ind : 
  "concat_language lang1 lang2 lst = concat_ind lang1 lang2 lst"
  apply (subst concat_iff_ex_app)
  apply (rule iffI)
   apply (rule ex2E)
  defer
    apply (simp)
   apply (rule concat_ind.induct[of lang1 lang2 lst])
    apply simp
   apply (rule_tac x = "lst1" in exI)
   apply (rule_tac x = "lst2" in exI)
   apply (auto)
  apply (erule ssubst)
  apply (rule concat_conj; simp)
  done

lemma concat_eps_eps [simp] : "concat_language_helper (\<lambda> l. l=[]) (\<lambda> l. l=[]) p l = (p @ l = [])"
  by (induction l arbitrary:p; simp)

lemma concat_empty_l [simp] : "concat_language_helper (\<lambda> l. False) lang p l = False"
  by (induction l arbitrary:p; simp)

lemma concat_empty_r [simp] : "concat_language_helper lang (\<lambda> l. False) p l = False"
  by (induction l arbitrary:p; simp)


lemma c_iff_eps : "regex_language (c r) = 
  (if (regex_language r []) then (\<lambda> l. l = []) else (\<lambda> l. False))"
  apply (induction r)
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  apply (simp only: c.simps regex_language.simps)
  apply (erule ssubst)
  apply (erule ssubst)
  by (rule funext; simp)

inductive many_ind :: "language \<Rightarrow> language" where
  many_nil : "many_ind lang []" | 
  many_prep : "lang prefix \<Longrightarrow> many_ind lang lst
  \<Longrightarrow> many_ind lang (prefix@lst)" 

inductive many_ind_nonempty :: "language \<Rightarrow> language" where
  many_ne_nil : "many_ind_nonempty lang []" | 
  many_ne_prep : "lang prefix \<Longrightarrow> prefix \<noteq> [] \<Longrightarrow> many_ind_nonempty lang lst
  \<Longrightarrow> many_ind_nonempty lang (prefix@lst)" 


lemma many_lang : "lang lst \<Longrightarrow> many_ind lang lst"
  apply (frule many_prep)
   apply (rule many_nil)
  by auto

lemma list_len_less_induct : 
  "(\<forall> lst. (\<forall> lst'. length lst' < length lst \<longrightarrow> P lst') \<longrightarrow> P lst) \<Longrightarrow>
  P lst"
  apply (induction "length lst" arbitrary:lst rule:less_induct; auto)
  done

lemma list_len_less_induct' : 
  " P [] \<Longrightarrow>
  (\<forall> a lst. (\<forall> lst'. length lst' < length (a # lst) \<longrightarrow> P lst') \<longrightarrow> P (a # lst)) \<Longrightarrow>
  P lst"
  apply (rule_tac lst="lst" in list_len_less_induct)
  apply (intro allI)
  apply (case_tac lst; auto)
  done

lemma dupasm : "A \<Longrightarrow> A"
  by simp

lemma impiffI : "P \<longrightarrow> Q \<Longrightarrow> Q \<longrightarrow> P \<Longrightarrow> P = Q"
  by auto

lemma many_lang_of_lang : "lang lst \<Longrightarrow> many_language lang lst"
  by (simp; rule many_language_of_lang; auto)

lemma many_of_ind : "many_ind lang lst \<Longrightarrow> many_language lang lst"
  apply (rule many_ind.induct[of lang lst])
  subgoal by auto
  subgoal by (auto)
  apply (rule many_language_app_of_lang_many; auto)
  done

lemma many_ind_iff_alt : "many_ind lang lst = many_ind_nonempty lang lst"
  apply (rule iffI)
   apply (erule many_ind.induct)
  subgoal by (rule many_ne_nil)
   apply (case_tac "prefix")
  apply (simp)
   apply (rule many_ne_prep; auto)
  apply (erule many_ind_nonempty.induct)
   apply (rule many_nil)
  by (rule many_prep; simp)

lemma many_ind_of_many : "\<forall> prefix. many_language_helper lang prefix lst \<longrightarrow> many_ind lang (prefix @ lst)"
  apply (rule list_len_less_induct'[of "(\<lambda> x. \<forall> p. many_language_helper lang p x \<longrightarrow> many_ind lang (p@x))" lst])
   apply (intro allI; rule impI)
   apply (subst (asm) many_helper_lst_nil; auto) 
    apply (rule many_nil)
   apply (rule many_lang; auto)
  apply (subst many_helper_prefix_Cons)
  apply (auto)
  apply (rule many_prep[of lang])
    apply (auto)
  apply (frule_tac x="lst" in spec)
   apply (drule mp)
  
    apply (auto)[]

   apply (frule_tac x="[a]" in spec) back
   apply (auto)
  apply (drule_tac x="lst" in spec)
  apply (drule mp)
  subgoal by auto
  apply (drule_tac x="prefix @ [a]" in spec; simp)
  done
 

lemma many_iff_ind : "many_language lang lst = many_ind lang lst"
  apply (rule impiffI)
   apply (insert many_ind_of_many[of lang lst]; auto)
  apply (insert many_of_ind; auto)
  done

lemma many_eq_ind : "many_language lang = many_ind lang"
  by (rule funext, rule allI, subst many_iff_ind; simp)

lemma concat_eq_ind : "concat_language lang1 lang2 = concat_ind lang1 lang2"
  by (rule funext, rule allI, subst concat_iff_ind; simp)


fun dby :: "bool \<Rightarrow> regex \<Rightarrow> regex" where
  "dby a Empty = Empty" |
  "dby a Eps = Empty" |
  "dby a (Char b) = (if a=b then Eps else Empty)" |
  "dby a (Plus r s) = Plus (dby a r) (dby a s)" |
  "dby a (Concat r s) = Plus (Concat (dby a r) s) (Concat (c r) (dby a s))" |
  "dby a (Many r) = Concat (dby a r) (Many r)"

fun invlang :: "bool list \<Rightarrow> language \<Rightarrow> language" where
  "invlang prefix lang = (\<lambda> l. lang (prefix @ l))"

lemma Many_to_Plus : "regex_language (Many r) = regex_language (Plus Eps (Concat r (Many r)))"
  apply (simp only: regex_language.simps)
  apply (rule funext; rule allI; rename_tac "lst")
  apply (subst many_iff_ex; subst concat_iff_ex_app)
  by simp

lemma invlang_plus : "invlang p (\<lambda> l. (P l \<or> Q l)) = (\<lambda> l. invlang p P l \<or> invlang p Q l)"
  by (rule funext; auto)

lemma impexE : "(\<forall> x. P x \<longrightarrow> Q) \<Longrightarrow> (\<exists> x. P x) \<longrightarrow> Q"
  by simp

lemma impdisjE : "P \<longrightarrow> R \<Longrightarrow> Q \<longrightarrow> R \<Longrightarrow> P \<or> Q \<longrightarrow> R"
  by simp

lemma invlang_char_concat : "invlang [a] (concat_language lang1 lang2) = 
  (\<lambda> l. (lang1 [] \<and> invlang [a] lang2 l) \<or> (concat_language (invlang [a] lang1) lang2) l)"
  apply (rule funext; rule allI; rename_tac "lst")
  apply (unfold invlang.simps)
  apply (subst (1 2) concat_iff_ex_app)
  apply (rule impiffI)
   apply (rule impexE; rule allI; rule impexE; rule allI)
   apply (case_tac l1; erule ssubst; auto)
  apply (rule impdisjE; auto)
  apply (rule_tac x="a#l1" in exI; auto)
  done
  

lemma invlang_cons_empty [simp] : "invlang (a#lst) (\<lambda> l. l = []) = (\<lambda> l. False)"
  by auto

lemma many_language_cons : 
  "many_language lang (a#lst) = concat_language (invlang [a] lang) (many_language lang) lst"
  apply (subst many_iff_ex; subst concat_iff_ex_app)
  apply (rule impiffI)
   apply (rule impdisjE)
  subgoal by auto
   apply (rule impexE; rule allI; rule impexE; rule allI)
   apply (case_tac l1; erule ssubst)
    apply (auto)
  subgoal by (subst (asm) many_helper_iff_ex; auto)
  apply (rule_tac x="a#l1" in exI)
  apply (rule_tac x=l2 in exI; auto)
  done

lemma many_ind_app' : "many_ind lang lst1 \<Longrightarrow> many_ind lang lst2 \<longrightarrow> many_ind lang (lst1 @ lst2)"
  apply (erule many_ind.induct[of lang lst1])
   apply (rule impI; auto)
  apply (simp)
  apply (rule impI; rule many_prep; auto)
  done
  
lemma many_ind_app : "many_ind lang lst1 \<Longrightarrow> many_ind lang lst2 \<Longrightarrow> many_ind lang (lst1 @ lst2)"
  by (insert many_ind_app'; auto)



lemma many_language_app_of_many : 
  "many_language lang lst1 \<Longrightarrow> many_language lang lst2 \<Longrightarrow>
  many_language lang (lst1 @ lst2)"
  
  apply (subst many_iff_ind; subst (asm) many_iff_ind; subst (asm) many_iff_ind)
  apply (frule many_ind_app[of lang lst1 lst2]; auto)
  done

lemma helper_of_many : 
  "many_language lang lst \<Longrightarrow> many_language_helper lang [] lst"
  by simp

lemma many_helper_to_many : "many_language_helper lang [] lst = many_language lang lst"
  by simp

lemma many_helper_of_many_cons : "many_language lang (a#lst) \<Longrightarrow> many_language_helper lang [a] lst"
  by simp

lemma cons_app : "a # l @ l' = (a # l) @ l'"
  by simp

lemma dby_correct : "regex_language (dby a r) = invlang [a] (regex_language r)"
  apply (induction r)
  subgoal by simp
  subgoal by simp
  subgoal by simp
  defer
  subgoal by simp
   apply (simp only: dby.simps regex_language.simps)
  apply (simp only: concat_iff_ex_app c_iff_eps; auto)
   (*apply (subst concat_iff_ind; subst concat_iff_ind; subst concat_eq_ind)*)
   apply (erule ssubst, erule ssubst, rule funext, rule allI)
    apply (auto)[]
     apply (rule_tac x="a#l1" in exI; rule_tac x=l2 in exI; auto)
    apply (case_tac l1; case_tac l2; auto)
   apply (erule ssubst, erule ssubst, rule funext, rule allI; auto)
     apply (rule_tac x="a#l1" in exI; rule_tac x=l2 in exI; auto)
   apply (case_tac l1; case_tac l2; auto)
  apply (simp only: dby.simps) 
  apply (subst Many_to_Plus)
  apply (simp only: regex_language.simps)
  apply (subst invlang_plus)
  apply (simp only: invlang_cons_empty)
  apply (subst invlang_char_concat)
  apply (subst concat_iff_ex_app)
  apply (erule ssubst)
  apply (rule funext; rule allI; rename_tac "lst")
  apply (subst concat_iff_ex_app)
  apply (unfold invlang.simps)
  apply (subst many_iff_ex)
  apply (auto)
  apply (drule_tac x=l1 in spec)
  apply (drule mp; auto)
  apply (drule_tac x=l1 in spec)
  apply (drule mp; auto)
  apply (drule_tac x=l1 in spec)
     apply (drule mp; auto)
     apply (subst (asm) (1 2) many_helper_to_many)
  apply (drule notE)
      apply (rule many_language_app_of_lang_many; auto)
     apply (auto)
    apply (subst (asm) (1 2) many_helper_to_many)
    apply (rule many_helper_of_many_cons)
  apply (subst cons_app)
    apply (rule many_language_app_of_lang_many)
  subgoal by auto
    apply (rule many_language_app_of_lang_many; auto)
   apply (subst (asm) many_helper_iff_ex; auto)
   apply (rule_tac x=l1 in exI; auto)
  apply (rule_tac x="l1" in exI)
  apply (rule_tac x=l2 in exI)
  apply (simp)
  apply (subst (asm) many_helper_iff_ex; auto)
  done



lemma many_ind_rev_imp : "many_ind lang lst \<Longrightarrow> many_ind (rev_language lang) (rev lst)"
  apply (erule many_ind.induct)
  subgoal by (simp; rule many_nil)
  apply (simp; rule many_ind_app)
   apply (auto)
  apply (rule many_lang; simp)
  done

lemma rev_rev_language [simp] : "rev_language (rev_language lang) = lang"
  by (rule funext; auto)

lemma many_language_rev_language : 
  "many_language (rev_language lang) lst 
    = (many_language lang) (rev lst)"
  apply (subst many_eq_ind)
  apply (subst many_eq_ind)
  apply (rule iffI; drule many_ind_rev_imp; simp)
  done

definition regex_example :: "regex" where
  "regex_example = Concat (Many (Plus (Char False) (Char True))) (Char False)"

lemma rev_corr_Many : "(\<forall> l. rev_corr r l) \<Longrightarrow> rev_corr (Many r) l"
  apply (simp del: many_language.simps)
  apply (drule funext)
  apply (erule ssubst)
  apply (insert many_language_rev_language[of "regex_language r" l])
  apply (erule ssubst)
  apply (subgoal_tac "(\<lambda>a. regex_language r (rev a)) = rev_language (regex_language r)")
   apply (erule ssubst; rule many_language_rev_language)
  apply (rule funext; auto)
  done


lemma rev_is_corr : "rev_corr r l" (is "?P r l")
  apply (induction r arbitrary: l)
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (rule rev_corr_Many; auto)
  subgoal by simp
  apply (rule rev_corr_Concat_ind; auto)
  done

lemma Rev_correct : "rev_language (regex_language r) l = regex_language (Rev r) l"
  apply (insert rev_is_corr[of r l])
  by simp

fun pumping_constant :: "regex \<Rightarrow> nat" where
  "pumping_constant Empty = 1" | 
  "pumping_constant Eps = 1" |
  "pumping_constant (Char n) = 2" |
  "pumping_constant (Many r) = 
    pumping_constant r" |
  "pumping_constant (Plus r s) = 
    pumping_constant r + pumping_constant s" |
  "pumping_constant (Concat r s) = 
    pumping_constant r + pumping_constant s" 

lemma pumping_constant_pos : "0 < pumping_constant r"
  by (induction r; simp)

fun napp :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "napp n l = concat (replicate n l)"

lemma napp_plus : "napp (n+m) l = napp n l @ napp m l"
  by (simp add: replicate_add)

lemma napp_star : "lang l1 \<Longrightarrow> many_language lang l2 \<Longrightarrow>
  many_language lang (napp m l1 @ l2)"
  apply (induction m)
  subgoal by simp
  apply (simp del:many_language.simps)
  apply (rule many_language_app_of_lang_many)
  by simp

lemma many_napp : "lang lst \<Longrightarrow> many_language lang (napp m lst)"
  apply (induction m)
  subgoal by simp
  apply (simp del:many_language.simps)
  apply (rule many_language_app_of_lang_many)
  by simp

lemma many_napp_many : "many_language lang lst \<Longrightarrow> many_language lang (napp m lst)"
  apply (induction m)
  subgoal by simp
  apply (simp del:many_language.simps)
  apply (rule many_language_app_of_many)
  by simp

lemma many_iff_opt_ex : 
  "many_language lang lst = 
    (lst = [] \<or> lang lst \<or> (\<exists> l1 l2. lst = l1@l2 \<and> lang l1 \<and> many_language lang l2))"
  apply (subst many_iff_ex)
  apply (auto)
  apply (drule spec)
  apply (drule mp)
   apply (simp)
  apply (drule spec[of _ "[]"])
  by simp



lemma many_opt_ex_not_nil : 
  "many_language lang lst \<Longrightarrow> lst \<noteq> [] \<longrightarrow>
  (\<exists> l1 l2. lst = l1@l2 \<and> l1 \<noteq> [] \<and> lang l1 \<and> many_language lang l2)"
  apply (subst (asm) many_iff_ind)
  apply (subst (asm) many_ind_iff_alt)
  apply (erule many_ind_nonempty.induct)
  subgoal by simp
  apply (auto)
  apply (rule_tac x="prefix" in exI)
  apply (rule_tac x="lst" in exI)
  apply (auto)
  apply (drule many_of_ind)
  by simp

lemma many_iff_opt_ex_not_nil : 
  "many_language lang lst =
  (lst = [] \<or> (\<exists> l1 l2. lst = l1@l2 \<and> l1 \<noteq> [] \<and> lang l1 \<and> many_language lang l2))"
  apply (insert many_opt_ex_not_nil)
  apply (auto)
  apply (rule many_language_app_of_lang_many_helper)
  by auto


lemma imp_swap : "P \<longrightarrow> Q \<longrightarrow> R = Q \<longrightarrow> P \<longrightarrow> R"
  by simp

lemma weak_pumping_many : 
  "\<forall>l. regex_language (Many r) l \<longrightarrow>
       pumping_constant (Many r) \<le> length l \<longrightarrow>
       (\<exists>s1 s2 s3.
           l = s1 @ s2 @ s3 \<and>
               s2 \<noteq> [] \<and> (\<forall>m. regex_language (Many r) (s1 @ napp m s2 @ s3)))"
  apply (intro allI)
  apply (rule impI; rule impI)
  apply (rule exI[of _ "[]"])
   apply (rule_tac x="l" in exI)
  apply (rule exI[of _ "[]"])
  apply (simp add: pumping_constant_pos)
  apply (rule conjI)
  apply (insert pumping_constant_pos[of r])[]
   apply (case_tac l; simp)
  apply (intro allI)
  apply (insert many_napp_many[of "regex_language r"])
  by simp


lemma plus_le_plusE : "(a :: nat) + b \<le> d + e \<Longrightarrow> (a \<le> d) \<or> (b \<le> e)"
  by auto


lemma weak_pumping : "\<forall> l. regex_language r l \<longrightarrow> pumping_constant r \<le> length l
  \<longrightarrow> (\<exists> s1 s2 s3. l = s1 @ s2 @ s3 \<and> s2 \<noteq> [] 
      \<and> (\<forall> m. regex_language r (s1 @ napp m s2 @ s3)))"
  apply (induction r)
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (rule weak_pumping_many)
   apply (intro allI; rule impI)
   apply (simp only: regex_language.simps)
   apply (erule disjE)
    apply (drule_tac x=l in spec)
    apply (drule_tac mp)
     apply (simp)
    apply (rule impI)
    apply (drule_tac mp)
     apply (simp)
  apply (erule exE; erule exE; erule exE)
  apply (rule_tac x=s1 in exI;
    rule_tac x=s2 in exI;
    rule_tac x=s3 in exI)
    apply (auto)[]
  apply (thin_tac " \<forall>l. regex_language r1 l \<longrightarrow>
           pumping_constant r1 \<le> length l \<longrightarrow>
           (\<exists>s1 s2 s3.
               l = s1 @ s2 @ s3 \<and> s2 \<noteq> [] \<and> (\<forall>m. regex_language r1 (s1 @ napp m s2 @ s3)))")
  apply (drule_tac x=l in spec)
    apply (drule_tac mp)
     apply (simp)
    apply (rule impI)
    apply (drule_tac mp)
     apply (simp)
  apply (erule exE; erule exE; erule exE)
  apply (rule_tac x=s1 in exI;
    rule_tac x=s2 in exI;
    rule_tac x=s3 in exI)
   apply (auto)[]

(* Case of concat... *)
  apply (intro allI)
  apply (rule impI)
  apply (simp only: regex_language.simps)
  apply (subst (asm) concat_iff_ex_app)
  apply (erule exE; erule exE; erule conjE)
  apply (erule ssubst)
  apply (simp only: pumping_constant.simps length_append)
  apply (rule impI)
  apply (drule plus_le_plusE)
  apply (erule disjE)
(* Case first splits *)
  apply (drule_tac x=l1 in spec)
   apply (drule mp)
  subgoal by simp
   apply (drule mp)
  subgoal by simp
  apply (erule exE; erule exE; erule exE)
  apply (rule_tac x=s1 in exI;
    rule_tac x=s2 in exI;
    rule_tac x="s3@l2" in exI)
   apply (auto)[]
   apply (subst concat_helper_iff_ex_app)
   apply (rule_tac x="s1 @ concat (replicate m s2) @ s3" in exI)
   apply (rule_tac x="l2" in exI)
  subgoal by auto
(* Case second splits *)
  apply (thin_tac "\<forall>l. regex_language r1 l \<longrightarrow> 
        pumping_constant r1 \<le> length l \<longrightarrow>
           (\<exists>s1 s2 s3.
               l = s1 @ s2 @ s3 \<and> s2 \<noteq> [] \<and> (\<forall>m. regex_language r1 (s1 @ napp m s2 @ s3)))")
  apply (drule_tac x=l2 in spec)
   apply (drule mp)
  subgoal by simp
   apply (drule mp)
  subgoal by simp
  apply (erule exE; erule exE; erule exE)
  apply (rule_tac x="l1@s1" in exI;
    rule_tac x=s2 in exI;
    rule_tac x="s3" in exI)
   apply (auto)[]
   apply (subst concat_helper_iff_ex_app)
   apply (rule_tac x="l1" in exI)
   apply (rule_tac x="s1 @ concat (replicate m s2) @ s3" in exI)
  by auto


lemma le_dec : "(n::nat) \<le> m \<or> m < n"
  by auto

lemma lt_dec : "(n::nat) < m \<or> m \<le> n"
  by auto

lemma impthinI : "Q \<Longrightarrow> P \<longrightarrow> Q"
  by simp

lemma append_invassoc : "xs @ ys @ zs = (xs @ ys) @ zs"
  by simp

lemma pumping : "\<forall> l. regex_language r l \<longrightarrow> pumping_constant r \<le> length l
  \<longrightarrow> (\<exists> s1 s2 s3. l = s1 @ s2 @ s3 \<and> s2 \<noteq> [] 
      \<and> length (s1) + length (s2) \<le> pumping_constant r
      \<and> (\<forall> m. regex_language r (s1 @ napp m s2 @ s3)))"
  apply (induction r)
  subgoal by simp
  subgoal by simp
  subgoal by simp
(* Case of Many *)
  apply (rule allI; simp only: regex_language.simps)
    apply (subst many_iff_ind; subst many_ind_iff_alt)
    apply (rule impI)
    apply (erule_tac many_ind_nonempty.cases)
  subgoal by (simp add: pumping_constant_pos)
    apply (rule impthinI)
    apply (insert le_dec)[]
    apply (drule_tac x="length prefix" in meta_spec)
    apply (drule_tac x="pumping_constant r" in meta_spec)
    apply (erule disjE)
  (* Case prefix small *)
     apply (rule exI[of _ "[]"])
     apply (rule_tac x="prefix" in exI)
     apply (rule_tac x="lst" in exI)
     apply (auto)[]
     apply (rule helper_of_many)
     apply (rule many_language_app_of_many)
  subgoal by (insert many_napp; auto)
  subgoal by (rule many_of_ind; subst many_ind_iff_alt; auto)
  (* case prefix big *)
      apply (drule_tac x="prefix" in spec)
      apply (drule mp)
      subgoal by simp
      apply (drule mp)
      subgoal by simp

        apply (erule exE; erule exE; erule exE)
        apply (rule_tac x="s1" in exI)
        apply (rule_tac x="s2" in exI)
        apply (rule_tac x="s3@lst" in exI)
        apply (simp del: many_language.simps)
        apply (intro allI)
        apply (subst (1 2) append_invassoc)
        apply (rule many_language_app_of_many)
         apply (rule many_lang_of_lang)
      subgoal by auto
      subgoal by (rule many_of_ind; subst many_ind_iff_alt; auto)
(* Case of Plus *)
   apply (intro allI; rule impI)
   apply (simp only: regex_language.simps)
   apply (erule disjE)
    apply (drule_tac x=l in spec)
    apply (drule_tac mp)
     apply (simp)
    apply (rule impI)
    apply (drule_tac mp)
     apply (simp)
  apply (erule exE; erule exE; erule exE)
  apply (rule_tac x=s1 in exI;
    rule_tac x=s2 in exI;
    rule_tac x=s3 in exI)
    apply (auto)[]
  apply (thin_tac " \<forall>l. regex_language r1 l \<longrightarrow>
           pumping_constant r1 \<le> length l \<longrightarrow>
           (\<exists>s1 s2 s3. l = s1 @ s2 @ s3 \<and> s2 \<noteq> [] 
  \<and> length s1 + length s2 \<le> pumping_constant r1 \<and> (\<forall>m. regex_language r1 (s1 @ napp m s2 @ s3)))")
  apply (drule_tac x=l in spec)
    apply (drule_tac mp)
     apply (simp)
    apply (rule impI)
    apply (drule_tac mp)
     apply (simp)
  apply (erule exE; erule exE; erule exE)
  apply (rule_tac x=s1 in exI;
    rule_tac x=s2 in exI;
    rule_tac x=s3 in exI)
   apply (auto)[]
(* Case of Concat... *)

  apply (intro allI)
  apply (rule impI)
  apply (simp only: regex_language.simps)
  apply (subst (asm) concat_iff_ex_app)
  apply (erule exE; erule exE; erule conjE)
  apply (erule ssubst)
  apply (simp only: pumping_constant.simps length_append)

    apply (insert le_dec)[]
    apply (drule_tac x="length l1" in meta_spec)
    apply (drule_tac x="pumping_constant r1" in meta_spec)
    apply (erule disjE)
  (* case l1 short *)
      apply (thin_tac "\<forall>l. regex_language r1 l \<longrightarrow>
           pumping_constant r1 \<le> length l \<longrightarrow> (\<exists>s1 s2 s3. l = s1 @ s2 @ s3 \<and> s2 \<noteq> [] \<and> length s1 + length s2 \<le> pumping_constant r1 \<and> (\<forall>m. regex_language r1 (s1 @ napp m s2 @ s3)))")
       apply (drule_tac x=l2 in spec)
      apply (rule impI)
       apply (drule mp)
      subgoal by simp
       apply (drule mp)
      subgoal by simp
      apply (erule exE; erule exE; erule exE)
      apply (rule_tac x="l1@s1" in exI;
        rule_tac x=s2 in exI;
        rule_tac x="s3" in exI)
       apply (simp del: concat_language.simps)
       apply (intro allI)
      apply (subst concat_iff_ex_app)
       apply (rule_tac x="l1" in exI;
        rule_tac x="s1@concat (replicate m s2)@s3" in exI)
      subgoal by simp
  (* case l1 long *)
      apply (drule_tac x=l1 in spec)
      apply (rule impI)
       apply (drule mp)
      subgoal by simp
       apply (drule mp)
      subgoal by simp
      apply (erule exE; erule exE; erule exE)
      apply (rule_tac x="s1" in exI;
        rule_tac x=s2 in exI;
        rule_tac x="s3@l2" in exI)
       apply (simp del: concat_language.simps)
       apply (intro allI)
      apply (subst concat_iff_ex_app)
       apply (rule_tac x="s1@concat (replicate m s2)@s3" in exI;
        rule_tac x="l2" in exI)
      by simp

lemma pumping_strong : "\<forall> l. regex_language r l \<longrightarrow> pumping_constant r \<le> length l
  \<longrightarrow> (\<exists> s1 s2 s3. l = s1 @ s2 @ s3 \<and> s2 \<noteq> [] 
      \<and> length (s1) + length (s2) < pumping_constant r
      \<and> (\<forall> m. regex_language r (s1 @ napp m s2 @ s3)))"
  apply (induction r)
  subgoal by simp
  subgoal by simp
  subgoal by simp
(* Case of Many *)
  apply (rule allI; simp only: regex_language.simps)
    apply (subst many_iff_ind; subst many_ind_iff_alt)
    apply (rule impI)
    apply (erule_tac many_ind_nonempty.cases)
  subgoal by (simp add: pumping_constant_pos)
    apply (rule impthinI)
    apply (insert lt_dec)[]
    apply (drule_tac x="length prefix" in meta_spec)
    apply (drule_tac x="pumping_constant r" in meta_spec)
    apply (erule disjE)
  (* Case prefix small *)
     apply (rule exI[of _ "[]"])
     apply (rule_tac x="prefix" in exI)
     apply (rule_tac x="lst" in exI)
     apply (auto)[]
     apply (rule helper_of_many)
     apply (rule many_language_app_of_many)
  subgoal by (insert many_napp; auto)
  subgoal by (rule many_of_ind; subst many_ind_iff_alt; auto)
  (* case prefix big *)
      apply (drule_tac x="prefix" in spec)
      apply (drule mp)
      subgoal by simp
      apply (drule mp)
      subgoal by simp

        apply (erule exE; erule exE; erule exE)
        apply (rule_tac x="s1" in exI)
        apply (rule_tac x="s2" in exI)
        apply (rule_tac x="s3@lst" in exI)
        apply (simp del: many_language.simps)
        apply (intro allI)
        apply (subst (1 2) append_invassoc)
        apply (rule many_language_app_of_many)
         apply (rule many_lang_of_lang)
      subgoal by auto
      subgoal by (rule many_of_ind; subst many_ind_iff_alt; auto)
(* Case of Plus *)
   apply (intro allI; rule impI)
   apply (simp only: regex_language.simps)
   apply (erule disjE)
    apply (drule_tac x=l in spec)
    apply (drule_tac mp)
     apply (simp)
    apply (rule impI)
    apply (drule_tac mp)
     apply (simp)
  apply (erule exE; erule exE; erule exE)
  apply (rule_tac x=s1 in exI;
    rule_tac x=s2 in exI;
    rule_tac x=s3 in exI)
    apply (auto)[]
  apply (thin_tac " \<forall>l. regex_language r1 l \<longrightarrow>
           pumping_constant r1 \<le> length l \<longrightarrow>
           (\<exists>s1 s2 s3. l = s1 @ s2 @ s3 \<and> s2 \<noteq> [] 
  \<and> length s1 + length s2 < pumping_constant r1 \<and> (\<forall>m. regex_language r1 (s1 @ napp m s2 @ s3)))")
  apply (drule_tac x=l in spec)
    apply (drule_tac mp)
     apply (simp)
    apply (rule impI)
    apply (drule_tac mp)
     apply (simp)
  apply (erule exE; erule exE; erule exE)
  apply (rule_tac x=s1 in exI;
    rule_tac x=s2 in exI;
    rule_tac x=s3 in exI)
   apply (auto)[]
(* Case of Concat... *)

  apply (intro allI)
  apply (rule impI)
  apply (simp only: regex_language.simps)
  apply (subst (asm) concat_iff_ex_app)
  apply (erule exE; erule exE; erule conjE)
  apply (erule ssubst)
  apply (simp only: pumping_constant.simps length_append)

    apply (insert lt_dec)[]
    apply (drule_tac x="length l1" in meta_spec)
    apply (drule_tac x="pumping_constant r1" in meta_spec)
    apply (erule disjE)
  (* case l1 short *)
      apply (thin_tac "\<forall>l. regex_language r1 l \<longrightarrow>
           pumping_constant r1 \<le> length l \<longrightarrow> (\<exists>s1 s2 s3. l = s1 @ s2 @ s3 \<and> s2 \<noteq> [] 
      \<and> length s1 + length s2 < pumping_constant r1 \<and> (\<forall>m. regex_language r1 (s1 @ napp m s2 @ s3)))")
       apply (drule_tac x=l2 in spec)
      apply (rule impI)
       apply (drule mp)
      subgoal by simp
       apply (drule mp)
      subgoal by simp
      apply (erule exE; erule exE; erule exE)
      apply (rule_tac x="l1@s1" in exI;
        rule_tac x=s2 in exI;
        rule_tac x="s3" in exI)
       apply (simp del: concat_language.simps)
       apply (intro allI)
      apply (subst concat_iff_ex_app)
       apply (rule_tac x="l1" in exI;
        rule_tac x="s1@concat (replicate m s2)@s3" in exI)
      subgoal by simp
  (* case l1 long *)
      apply (drule_tac x=l1 in spec)
      apply (rule impI)
       apply (drule mp)
      subgoal by simp
       apply (drule mp)
      subgoal by simp
      apply (erule exE; erule exE; erule exE)
      apply (rule_tac x="s1" in exI;
        rule_tac x=s2 in exI;
        rule_tac x="s3@l2" in exI)
       apply (simp del: concat_language.simps)
       apply (intro allI)
      apply (subst concat_iff_ex_app)
       apply (rule_tac x="s1@concat (replicate m s2)@s3" in exI;
        rule_tac x="l2" in exI)
      by simp

end