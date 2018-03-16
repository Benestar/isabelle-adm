(*
  Author:   Benedikt Seidl
  License:  GPL-3.0-or-later
*)

theory Graph
  imports Main
begin

type_synonym 'a graph = "'a set \<times> 'a set set"

locale graph =
  fixes
    G :: "'a graph"
  fixes
    V :: "'a set"
  fixes
    E :: "'a set set"
  defines
    "V \<equiv> fst G"
  defines
    "E \<equiv> snd G"
  assumes
    finite_vertices: "finite V"
  assumes
    nonempty_vertices: "V \<noteq> {}"
  assumes
    edges: "E \<subseteq> {e. e \<subseteq> V \<and> card e = 2}"
begin

lemma finite_edges: "finite E"
proof -
  from finite_vertices have "finite {e. e \<subseteq> V}"
    by fast
  hence "finite {e. e \<subseteq> V \<and> card e = 2}"
    by fast
  with edges show "finite E"
    by (rule Finite_Set.finite_subset)
qed

lemma edge_vertices: "e \<in> E \<Longrightarrow> \<exists>v w. e = {v, w}"
proof -
  fix e assume "e \<in> E"

  then have "card e = Suc (Suc 0)" using edges by auto

  then obtain v e' where "e = insert v e'" and "card e' = Suc 0"
    using card_eq_SucD by metis

  then show "\<exists>v w. e = {v, w}"
    using card_eq_SucD
    by blast
qed

subsection \<open>Adjacency and Neighborhood\<close>

definition adjacent :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "adjacent v w \<equiv> {v, w} \<in> E"

definition neighborhood :: "'a \<Rightarrow> 'a set" where
  "neighborhood v \<equiv> {w \<in> V. {v, w} \<in> E}"

definition deg :: "'a \<Rightarrow> nat" where
  "deg v \<equiv> card {e \<in> E. v \<in> e}"

definition isolated :: "'a \<Rightarrow> bool" where
  "isolated v \<equiv> deg v = 0"

definition leaf :: "'a \<Rightarrow> bool" where
  "leaf v \<equiv> deg v = 1"

definition \<delta> :: nat where
  "\<delta> \<equiv> Min {deg v | v. v \<in> V}"

definition \<Delta> :: nat where
  "\<Delta> \<equiv> Max {deg v | v. v \<in> V}"

lemma adjacent_comm: "adjacent v w \<longleftrightarrow> adjacent w v"
proof -
  have "{v, w} = {w, v}"
    by fast
  thus "adjacent v w \<longleftrightarrow> adjacent w v"
    unfolding adjacent_def by simp
qed

lemma deg_card_neighborhood: "deg v = card (neighborhood v)"
proof -

  define f :: "'a \<Rightarrow> 'a set" where "f \<equiv> \<lambda>w. {v, w}"

  have "bij_betw f {w \<in> V. {v, w} \<in> E} {e \<in> E. v \<in> e}"
    unfolding bij_betw_def
  proof
    show "inj_on f {w \<in> V. {v, w} \<in> E}"
      unfolding inj_on_def f_def
      by (simp add: doubleton_eq_iff) 
  next
    show "f ` {w \<in> V. {v, w} \<in> E} = {e \<in> E. v \<in> e}"
      unfolding f_def image_def
    proof auto
      fix e
      assume "e \<in> E" and "v \<in> e"

      then obtain w where "e = {v, w}"
        using edge_vertices by blast

      then show "\<exists>w. w \<in> V \<and> {v, w} \<in> E \<and> e = {v, w}"
        using edges \<open>e \<in> E\<close> by blast
    qed
  qed

  then have "card {w \<in> V. {v, w} \<in> E} = card {e \<in> E. v \<in> e}"
    using bij_betw_same_card by auto

  then show ?thesis
    unfolding deg_def neighborhood_def by simp
qed

lemma sum_deg: "(\<Sum>v \<in> V. deg v) = 2 * card E"
  oops

lemma even_edges_odd: "even (card {v \<in> V. odd (deg v)})"
  oops

lemma same_deg: "card V \<ge> 2 \<Longrightarrow> \<exists>v \<in> V. \<exists>w \<in> V. v \<noteq> w \<and> deg v = deg w"
  oops

subsection \<open>Subgraphs and Isomorphism\<close>

definition subgraph :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "subgraph W F \<equiv> graph (W, F) \<and> W \<subseteq> V \<and> F \<subseteq> E"

definition induced_subgraph :: "'a set \<Rightarrow> 'a set \<times> 'a set set" where
  "induced_subgraph W \<equiv> (V \<inter> W, {e \<in> E. e \<subseteq> W})"

definition isomorphic :: "'b set \<Rightarrow> 'b set set \<Rightarrow> bool" where
  "isomorphic W F \<equiv> graph (W, F) \<and> (\<exists>f. \<forall>v \<in> V. \<forall>w \<in> V. {v, w} \<in> E \<longleftrightarrow> {f v, f w} \<in> F)"

end

subsection \<open>Notation\<close>

abbreviation supgraph :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> bool" (infix "\<subseteq>\<^sub>G" 50) where
  "G \<subseteq>\<^sub>G H \<equiv> graph.subgraph H (fst G) (snd G)"

abbreviation induced_subgraph :: "'a graph \<Rightarrow> 'a set \<Rightarrow> 'a graph" ("_[_](\<^sub>G)" 51) where
  "G[V]\<^sub>G \<equiv> graph.induced_subgraph G V"

abbreviation isomorphic :: "'a graph \<Rightarrow> 'b graph \<Rightarrow> bool" (infix "\<sim>\<^sub>G" 50) where
  "G \<sim>\<^sub>G H \<equiv> graph.isomorphic G (fst H) (snd H)"


lemma "G[V]\<^sub>G \<subseteq>\<^sub>G G"
  oops

lemma isomorphic_comm: "G \<sim>\<^sub>G H \<longleftrightarrow> H \<sim>\<^sub>G G"
  oops

lemma isomorphic_card:
  assumes
    "graph (V, E)"
  assumes
    "graph (W, F)"
  assumes
    "(V, E) \<sim>\<^sub>G (W, F)"
  shows
    "card V = card W" and "card E = card F"
proof -
  show "card V = card W" sorry
next
  show "card E = card F" sorry
qed

subsection \<open>Special graphs\<close>

definition path :: "nat \<Rightarrow> nat graph" ("P\<^sub>G _" 1) where
  "path n = ({1..n}, {{i, i + 1} | i. i \<in> {1..n-1}})"

definition circle :: "nat \<Rightarrow> nat graph" ("C\<^sub>G _") where
  "circle n \<equiv> ({1..n}, {{i, i + 1} | i. i \<in> {1..n-1}} \<union> {{1, n}})"

definition complete :: "nat \<Rightarrow> nat graph" ("K\<^sub>G _") where
  "complete n = ({1..n}, {{v, w} | v w. v \<in> {1..n} \<and> w \<in> {1..n} \<and> v \<noteq> w})"

lemma[simp]: "graph (P\<^sub>G n)"
  sorry

lemma[simp]: "graph (C\<^sub>G n)"
  sorry

lemma[simp]: "graph (K\<^sub>G n)"
  sorry

lemma empty_edges[simp]: "finite V \<Longrightarrow> V \<noteq> {} \<Longrightarrow> graph (V, {})"
  unfolding graph_def by simp

context graph
begin

definition path :: bool where
  "path \<equiv> \<exists>n. G \<sim>\<^sub>G (P\<^sub>G n)"

definition circle :: bool where
  "circle \<equiv> \<exists>n \<ge> 3. G \<sim>\<^sub>G (C\<^sub>G n)"

definition complete :: bool where
  "complete \<equiv> \<exists>n. G \<sim>\<^sub>G (K\<^sub>G n)"

definition acyclic :: bool where
  "acyclic \<equiv> \<forall>H. H \<subseteq>\<^sub>G G \<longrightarrow> \<not> graph.circle H"

definition connected :: bool where
  "connected \<equiv> undefined"

definition tree :: bool where
  "tree \<equiv> acyclic \<and> connected"

definition spanning_tree :: "'a graph \<Rightarrow> bool" where
  "spanning_tree T \<equiv> T \<subseteq>\<^sub>G G \<and> graph.tree T \<and> V = fst T"

lemma connected_spanning_tree: "connected \<longleftrightarrow> (\<exists>T. spanning_tree T)"
  oops

end


end