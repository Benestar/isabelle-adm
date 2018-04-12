(*
  Author:   Benedikt Seidl
  License:  GPL-3.0-or-later
*)

theory Graph_Base
  imports Main
begin

locale graph_base =
  fixes
    G :: "'a set \<times> 'b set"
  fixes
    V :: "'a set" and E :: "'b set"
  defines
    "V \<equiv> fst G" and "E \<equiv> snd G"
  assumes
    finite_vertices: "finite V"
  assumes
    nonempty_vertices: "V \<noteq> {}"

  fixes
    adjacent :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes
    incident :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
begin

subsection \<open>Adjacency and Neighborhood\<close>

definition neighborhood :: "'a \<Rightarrow> 'a set" where
  "neighborhood v \<equiv> {w \<in> V. adjacent v w}"

definition deg :: "'a \<Rightarrow> nat" where
  "deg v \<equiv> card {e \<in> E. incident v e}"

definition isolated :: "'a \<Rightarrow> bool" where
  "isolated v \<equiv> deg v = 0"

definition leaf :: "'a \<Rightarrow> bool" where
  "leaf v \<equiv> deg v = 1"

definition \<delta> :: nat where
  "\<delta> \<equiv> Min {deg v | v. v \<in> V}"

definition \<Delta> :: nat where
  "\<Delta> \<equiv> Max {deg v | v. v \<in> V}"


subsection \<open>Subgraphs and Isomorphism\<close>

(* TODO: check if (W, F) is a graph *)
definition subgraph' :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "subgraph' W F \<equiv> W \<subseteq> V \<and> F \<subseteq> E"

definition induced_subgraph' :: "'a set \<Rightarrow> 'a set \<times> 'b set" where
  "induced_subgraph' W \<equiv> (V \<inter> W, {e \<in> E. \<forall>v. incident v e \<longrightarrow> v \<in> W})"

(* TODO: check if (W, F) is a graph *)
definition isomorphic' :: "'c set \<Rightarrow> 'd set \<Rightarrow> bool" where
  "isomorphic' W F \<equiv> (\<exists>f. \<forall>v \<in> V. \<forall>w \<in> V. adjacent v w \<longleftrightarrow> adjacent (f v) (f w))"

end



end