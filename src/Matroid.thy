(*
  Author:   Benedikt Seidl
  License:  GPL-3.0-or-later
*)

theory Matroid
  imports Main Graph
begin

locale independence_system =
  fixes
    E :: "'a set"
  fixes
    I :: "'a set set"
  assumes
    finite: "finite E"
  assumes
    subset: "I \<subseteq> Pow E"
  assumes
    nonempty: "I \<noteq> {}"
  assumes
    1: "B \<in> I \<Longrightarrow> A \<subseteq> B \<Longrightarrow> A \<in> I"
begin

  lemma "{} \<in> I"
    using nonempty 1 by blast

end

locale matroid = independence_system +
  assumes
    2: "\<forall>A \<in> I. \<forall>B \<in> I. card A < card B \<longrightarrow> (\<exists>e \<in> B - A. A \<union> {e} \<in> I)"
begin

end

lemma card_subset: "n \<le> card B \<Longrightarrow> \<exists>B' \<subseteq> B. card B' = n"
proof (induction n)
  case 0
  have "{} \<subseteq> B"
    by blast
  then show ?case
    using 0 by fastforce
next
  case (Suc n)
  hence "n < card B"
    by simp

  with Suc obtain B' where "B' \<subseteq> B" and "card B' = n"
    by auto

  with \<open>n < card B\<close> have "B' \<subset> B"
    by auto
  then obtain e where "e \<in> B - B'"
    by auto
  hence "e \<notin> B'" and "e \<in> B"
    by auto

  from \<open>n < card B\<close> have "0 < card B"
    by simp
  hence "finite B"
    using card_infinite by fastforce
  hence "finite B'"
    using \<open>B' \<subset> B\<close> finite_subset by auto

  with \<open>card B' = n\<close> \<open>e \<notin> B'\<close> have "card (B' \<union> {e}) = Suc n"
    by simp
  with \<open>B' \<subseteq> B\<close> \<open>e \<in> B\<close> have "(B' \<union> {e}) \<subseteq> B \<and> card (B' \<union> {e}) = Suc n"
    by simp
  thus ?case
    by blast
qed


lemma matroid_2':
  assumes "independence_system E I"
  shows "matroid E I \<longleftrightarrow> (\<forall>A \<in> I. \<forall>B \<in> I. card A + 1 = card B \<longrightarrow> (\<exists>e \<in> B - A. A \<union> {e} \<in> I))"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs

  hence 2: "\<forall>A \<in> I. \<forall>B \<in> I. card A < card B \<longrightarrow> (\<exists>e \<in> B - A. A \<union> {e} \<in> I)"
    using "matroid.2" by blast

  show ?rhs
  proof safe
    fix A B assume "A \<in> I" and "B \<in> I" and "card A + 1 = card B"
    thus "\<exists>e \<in> B - A. A \<union> {e} \<in> I" using 2 by simp
  qed
next
  assume ?rhs

  have "\<forall>A \<in> I. \<forall>B \<in> I. card A < card B \<longrightarrow> (\<exists>e \<in> B - A. A \<union> {e} \<in> I)"
  proof safe
    fix A B assume "A \<in> I" and "B \<in> I" and "card A < card B"
    then obtain n where "n = card A + 1"
      by blast
    hence "n \<le> card B"
      using \<open>card A < card B\<close> by fastforce
    then obtain B' where "B' \<subseteq> B" and "card B' = n"
      using card_subset by auto
    hence "\<exists>e \<in> B' - A. A \<union> {e} \<in> I"
      by (metis "independence_system.1" \<open>A \<in> I\<close> \<open>B \<in> I\<close> \<open>?rhs\<close> \<open>n = card A + 1\<close> assms)

    then show "\<exists>e \<in> B - A. A \<union> {e} \<in> I" using \<open>B' \<subseteq> B\<close> by blast
  qed

  thus ?lhs using assms matroid_def matroid_axioms_def by blast
qed

lemma
  fixes
    V :: "'a set"
  fixes
    E :: "'a set set"
  assumes
    g: "graph (V, E)"
  defines
    i: "I \<equiv> {F. F \<subseteq> E \<and> graph.acyclic (V, F)}"
  shows
    "matroid E I"
proof
  show "finite E"
    using g graph.finite_edges by fastforce
next
  show "I \<subseteq> Pow E"
    using i by auto
next
  thm graph.nonempty_vertices
  thm graph.acyclic_def
  thm empty_edges
  thm graph.subgraph_def

  have "graph (V, {})"
    using g graph.finite_vertices graph.nonempty_vertices empty_edges
    by fastforce

  have "\<forall>H. H \<subseteq>\<^sub>G (V, {}) \<longrightarrow> \<not> graph.circle H"
    proof safe
      fix W F assume s: "(W, F) \<subseteq>\<^sub>G (V, {})" and c: "graph.circle (W, F)"

      hence "graph (W, F) \<and> W \<subseteq> V \<and> F \<subseteq> {}"
        using \<open>graph (V, {})\<close> graph.subgraph_def by auto
      hence "graph (W, F)" and "F = {}"
        by simp+

      with c obtain n where "n \<ge> 3" and "(W, F) \<sim>\<^sub>G (C\<^sub>G n)"
        using graph.circle_def by blast

      hence "card F = card (snd (C\<^sub>G n))"
        using \<open>graph (W, F)\<close> isomorphic_card sorry

      hence "snd (C\<^sub>G n) = {}" using \<open>F = {}\<close> sorry

      thm \<open>F = {}\<close>

      show False sorry
    qed

  hence "graph.acyclic (V, {})"
    using \<open>graph (V, {})\<close> by (subst graph.acyclic_def)

  hence "{} \<in> I"
    using i by simp

  thus "I \<noteq> {}"
    by auto
next
  fix A
  show "A \<in> I" sorry
next
  show "\<forall>A\<in>I. \<forall>B\<in>I. card A < card B \<longrightarrow> (\<exists>e\<in>B - A. A \<union> {e} \<in> I)"
  proof safe
    fix A B
    show "\<exists>e\<in>B - A. A \<union> {e} \<in> I" sorry
  qed
qed

end