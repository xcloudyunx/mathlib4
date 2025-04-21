/-
Copyright (c) 2025 Yunge Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunge Yu
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Trails

namespace SimpleGraph

open Walk

variable {V : Type*} (G : SimpleGraph V)

variable [Fintype V] [DecidableRel G.Adj]

/-- A graph is a *cycle* if it is connected, every vertex has degree 2. -/
def IsCycleGraph : Prop := G.Connected ∧ (∀ (v : V), G.degree v = 2)

namespace IsCycleGraph

lemma Connected (c : G.IsCycleGraph) : G.Connected := by
  obtain ⟨hC, _⟩ := c
  exact hC

lemma all_vertices_degree_two (c : G.IsCycleGraph) : ∀ (v : V), G.degree v = 2 := by
  obtain ⟨_, hD⟩ := c
  exact hD

lemma vertex_card_eq_edge_card (c : G.IsCycleGraph) : Fintype.card V = Fintype.card G.edgeSet := by
  obtain ⟨hC, hD⟩ := c
  have hVCard : ∑ (v : V), G.degree v = 2*(Fintype.card V) := by
    simp [← Finset.card_univ]
    have hDLE : ∀ v ∈ (Finset.univ : Finset V), G.degree v ≤ 2 := by simp [hD]
    rw [Finset.card_eq_sum_ones, Finset.mul_sum, mul_one, Finset.sum_eq_sum_iff_of_le hDLE]
    simp
    exact hD
  have hECard : ∑ (v : V), G.degree v = 2*(Fintype.card G.edgeSet) := by
    simp
    have hHS : ∑ (v : V), G.degree v = 2*G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
    simp at hHS
    exact hHS
  have h : 2*(Fintype.card V) = 2*(Fintype.card G.edgeSet) := by rw [← hVCard, ← hECard]
  simp at h
  simp [h]

lemma three_le_card (c : G.IsCycleGraph) : 3 ≤ Fintype.card V := by
  obtain ⟨hC, hD⟩ := c
  rw [connected_iff] at hC
  obtain ⟨_, hNE⟩ := hC
  obtain ⟨v⟩ := hNE
  have hNC : (G.neighborFinset v).card < Fintype.card V :=
    Finset.card_lt_univ_of_not_mem (G.not_mem_neighborFinset_self v)
  rw [G.card_neighborFinset_eq_degree, hD] at hNC
  simp [Nat.add_one_le_iff, hNC]

variable {v w : V}

lemma IsCycles (c : G.IsCycleGraph) : G.IsCycles := by
  intro v
  obtain ⟨hC, hD⟩ := c
  have hNC : ∀ (v : V), Fintype.card (G.neighborSet v) = 2 := by
    simp [G.card_neighborSet_eq_degree]
    exact hD
  have hN : Fintype.card (G.neighborSet v) = 2 := by apply hNC
  have hNNE : (G.neighborSet v).Nonempty := by
    by_contra hFalse
    simp [Set.not_nonempty_iff_eq_empty] at hFalse
    have hNC0 : Fintype.card (G.neighborSet v) = 0 := by simp [hFalse]
    have hContra : 0 = 2 := by rw [← hNC0, ← hNC]
    contradiction
  simp at hN
  simp [hNNE, Set.ncard_eq_toFinset_card', hN]

lemma exists_adj (c : G.IsCycleGraph) : ∃ (w : V), G.Adj v w := by
  obtain ⟨hC, hD⟩ := c
  have hD : G.degree v > 0 := by
    rw [hD]
    trivial
  simp [G.degree_pos_iff_exists_adj] at hD
  exact hD

lemma neighbor_nonempty (c : G.IsCycleGraph) : (G.neighborSet v).Nonempty := by
  obtain ⟨w, hw⟩ := c.exists_adj
  have h4 : w ∈ G.neighborSet v := hw
  use w

lemma no_bridges (c : G.IsCycleGraph) (h : G.Adj v w) : ¬G.IsBridge s(v, w) := by
  have h1 : G.IsCycles := c.IsCycles
  have h3 : (G.deleteEdges {s(v, w)}).Reachable v w := by
    apply IsCycles.reachable_deleteEdges h h1
  simp [isBridge_iff, h]
  exact h3

lemma notTree (c : G.IsCycleGraph) : ¬G.IsTree := by
  simp [G.isTree_iff_connected_and_card, c.vertex_card_eq_edge_card]

lemma notAcyclic (c : G.IsCycleGraph) : ¬G.IsAcyclic := by
  have hT : ¬G.IsTree := c.notTree
  obtain ⟨hC, _⟩ := c
  simp [G.isTree_iff, hC] at hT
  exact hT

lemma isCyclic (c : G.IsCycleGraph) : ∃ (v : V) (p : G.Walk v v), p.IsCycle := by
  have hA : ¬G.IsAcyclic := c.notAcyclic
  unfold IsAcyclic at hA
  simp at hA
  exact hA

lemma all_vertices_form_a_cycle (c : G.IsCycleGraph) : ∃ (p : G.Walk v v), p.IsCycle := by
  have h2 : v ∈ G.connectedComponentMk v := ConnectedComponent.connectedComponentMk_mem
  have h3 : (G.neighborSet v).Nonempty := by
    obtain ⟨w, hw⟩ := c.exists_adj
    have h31 : w ∈ G.neighborSet v := hw
    use w
  obtain ⟨p, hpc, _⟩ :=
    IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp c.IsCycles h2 h3
  use p

lemma cycle_walk_contains_all_vertices {p : G.Walk v v} (c : G.IsCycleGraph) (h : p.IsCycle) :
    ∀ (v : V), v ∈ p.support := by
  intro w
  have hC : G.Connected := c.Connected
  have hvwR : G.Reachable v w := by
    have hR : ∀ (v w : V), G.Reachable v w := hC
    apply hR
  have h0 : p.toSubgraph.verts = (G.connectedComponentMk v).supp := by
    have h : ∀ v ∈ p.toSubgraph.verts, ∀ (w : V), G.Adj v w → p.toSubgraph.Adj v w := by
      intro v hv w hvw
      refine (Subgraph.adj_iff_of_neighborSet_equiv ?_ (Set.toFinite _)).mpr hvw
      have hNE: (G.neighborSet v).Nonempty := c.exists_adj
      refine @Classical.ofNonempty _ ?_
      rw [← Cardinal.eq, ← Set.cast_ncard (Set.toFinite _), ← Set.cast_ncard (Set.toFinite _),
        c.IsCycles G hNE, h.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp hv)]
    obtain ⟨cc, hcc⟩ := p.toSubgraph_connected.exists_verts_eq_connectedComponentSupp h
    rw [hcc]
    have : v ∈ cc.supp := by simp [← hcc]
    simp_all
  have h1 : w ∈ (G.connectedComponentMk v).supp := by
    have h11 : w ∈ (G.connectedComponentMk w) := ConnectedComponent.connectedComponentMk_mem
    have h12 : G.connectedComponentMk w = G.connectedComponentMk v := by
      rw [eq_comm]
      apply ConnectedComponent.sound
      exact hvwR
    have h13 : w ∈ (G.connectedComponentMk v) := by simp [← h12, h11]
    apply h13
  have h2 : w ∈ p.toSubgraph.verts := by
    rw [h0]
    exact h1
  rw [← mem_verts_toSubgraph]
  exact h2

lemma cycle_walk_tail_contains_all_vertices {p : G.Walk v v} (c : G.IsCycleGraph) (h : p.IsCycle) :
    ∀ (v : V), v ∈ p.support.tail := by
  have h0 : ∀ (v : V), v ∈ p.support ↔ v ∈ p.support.tail := by
    intro w
    constructor
    · intro h00
      have h1 : p.support ≠ [] := by simp
      by_cases h2 : w = p.support.head h1
      · simp at h2
        rw [h2]
        exact end_mem_tail_support h.not_nil
      · cases h6 : p.support with
        | nil => contradiction
        | cons head tail => simp_all
    · exact List.mem_of_mem_tail
  simp [← h0]
  exact c.cycle_walk_contains_all_vertices G h

variable [DecidableEq V]

lemma cycle_walk_contains_all_edges {p : G.Walk v v} (c : G.IsCycleGraph) (h : p.IsCycle) :
    ∀ e ∈ G.edgeSet, e ∈ p.edges := by
  have h8 : p.edges.Nodup := h.edges_nodup
  have h2 : p.support.tail.length = Fintype.card V := by
    have h21 : ∀ (v : V), v ∈ p.support.tail := c.cycle_walk_tail_contains_all_vertices G h
    have h22 : p.support.tail.Nodup := h.support_nodup
    have h23 : p.support.tail.toFinset.card = p.support.tail.length :=
      List.toFinset_card_of_nodup h22
    have h28 : ∀ (v : V), v ∈ p.support.tail.toFinset := by simp [h21]
    rw [← Finset.eq_univ_iff_forall] at h28
    have h29 : p.support.tail.toFinset.card = Fintype.card V := by simp [h28]
    rw [← h23]
    exact h29
  have h4 : p.edges.toFinset.card = p.edges.length := List.toFinset_card_of_nodup h8
  have h3 : p.edges.length = p.length := p.length_edges
  have h5 : p.tail.length + 1 = p.length := p.length_tail_add_one h.not_nil
  have h6 : p.tail.support.length = p.tail.length + 1 := p.tail.length_support
  have h7 : p.support.tail.length = p.tail.support.length := by simp [p.support_tail h.not_nil]
  have h10 : Fintype.card G.edgeSet = G.edgeFinset.card := by simp
  rw [c.vertex_card_eq_edge_card, h7, h6, h5, ← h3, ← h4, h10] at h2
  have h9 : p.edges.toFinset ⊆ G.edgeFinset := by
    simp
    apply edges_subset_edgeSet
  have h12 : G.edgeFinset.card ≤ p.edges.toFinset.card := Eq.ge h2
  have h11 : p.edges.toFinset = G.edgeFinset := Finset.eq_of_subset_of_card_le h9 h12
  have h13 : p.edgeSet = G.edgeSet := by
    calc
      p.edgeSet = ↑p.edges.toFinset := by rw [coe_edges_toFinset]
      _ = ↑G.edgeFinset := by rw [h11]
      _ = G.edgeSet := by rw [coe_edgeFinset]
  have h14 : ∀ e ∈  G.edgeSet, e ∈ p.edgeSet := by simp [h13]
  simp at h14
  exact h14

theorem isEulerian (c : G.IsCycleGraph) : ∃ (v : V) (p : G.Walk v v), p.IsEulerian
    := by
  simp [isEulerian_iff]
  obtain ⟨v, p, hC⟩ := c.isCyclic
  use v
  use p
  have hT : p.IsTrail := by apply IsCircuit.isTrail (IsCycle.isCircuit hC)
  simp [hT]
  exact c.cycle_walk_contains_all_edges G hC

lemma isHamiltonian (c : G.IsCycleGraph) : G.IsHamiltonian := by
  unfold IsHamiltonian
  intro
  simp [isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one]
  obtain ⟨v, p, hC⟩ := c.isCyclic
  use v
  use p
  simp [hC]
  have h : ∀ (v : V), List.count v p.support.tail = 1 := by
    intro v
    have h : v ∈ p.support.tail := by apply c.cycle_walk_tail_contains_all_vertices G hC
    apply List.count_eq_one_of_mem hC.support_nodup h
  exact h

end IsCycleGraph

lemma Walk.IsCycle.coe_subgraph_is_cycle_graph {v : V} (p : G.Walk v v) [Fintype p.toSubgraph.verts]
    [DecidableRel p.toSubgraph.coe.Adj] (h : p.IsCycle) : p.toSubgraph.coe.IsCycleGraph := by
  have h1 : p.toSubgraph.coe.Connected := p.toSubgraph_connected.coe
  have h2 : ∀ v ∈ p.support, (p.toSubgraph.neighborSet v).ncard = 2 := by
    intro v hv
    exact h.ncard_neighborSet_toSubgraph_eq_two hv
  have h3 : ∀ v ∈ p.toSubgraph.verts, (p.toSubgraph.neighborSet v).ncard = 2 := by
    intro v hv
    rw [mem_verts_toSubgraph] at hv
    apply h2
    exact hv
  have h4 : ∀ (v : ↑p.toSubgraph.verts), (p.toSubgraph.coe.neighborSet v).ncard = 2 := by
    intro v
    have h41 := p.toSubgraph.coeNeighborSetEquiv v
    have h42 := v.prop
    have h43 := h3 v h42
    have h44 := h41.cardinal_eq
    unfold neighborSet at *
    unfold Subgraph.neighborSet at *
    simp at h41
    simp at h44
    simp
    simp [← Nat.cast_card, ← Nat.cast_card] at h44
    simp [← Set.Nat.card_coe_set_eq] at h43
    simp [← Set.Nat.card_coe_set_eq]
    rw [h44, h43]
  have h5 : ∀ (v : ↑p.toSubgraph.verts), (p.toSubgraph.coe.degree v) = 2 := by
    intro v
    rw [← card_neighborFinset_eq_degree]
    unfold neighborFinset
    rw [← Set.ncard_eq_toFinset_card']
    apply h4
  have h6 : p.toSubgraph.coe.Connected ∧
      ∀ (v : ↑p.toSubgraph.verts), (p.toSubgraph.coe.degree v) = 2 := by trivial
  exact h6

end SimpleGraph
