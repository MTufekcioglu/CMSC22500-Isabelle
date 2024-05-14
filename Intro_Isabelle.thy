theory Intro_Isabelle
  imports Main
begin

(* As calculator *)
value "(1::nat) + 1"

(* Natural numbers *)
value "(5::nat) - 6"



(* λ-expressions *)
value "(λ x y z. x + y + z + 1) 1 2 3::nat"



(* Lists and functions *)
fun count:: "'a list ⇒ 'a ⇒ nat" where
  "count[] _ = 0" |
  "count (x#xs) x' = (if x = x' then Suc (count xs x') else count xs x')"

value "count [0, 1, 0, 2, 0, 3] (0::nat)"

lemma "count [0, 1, 0, 2, 0, 3] (0::nat) = 3"
  apply auto
  done



(* Basic theorem *)
theorem ct_vs_len: "count xs x ≤ length xs"
  apply(induct xs)
  apply auto
  done

theorem prettier_ct_vs_len: "count xs x ≤ length xs"
  by (induct xs) auto



(* Data Types *)

datatype 'a my_tree = Leaf 'a | Node "'a my_tree" "'a my_tree"

term "Leaf (0::nat)"

term "Node 
      (Node 
        (Leaf (1::nat))
        (Leaf (2::nat)))
      (Leaf (3::nat))"
