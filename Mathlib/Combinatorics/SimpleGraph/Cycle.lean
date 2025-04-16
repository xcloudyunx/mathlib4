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
def IsCycle : Prop := G.Connected ∧ (∀ (v : V), G.degree v = 2)

namespace IsCycle

lemma Connected (c : G.IsCycle) : G.Connected := by
  obtain ⟨hC, _⟩ := c
  exact hC

lemma all_vert_degree_two (c : G.IsCycle) : ∀ (v : V), G.degree v = 2 := by
  obtain ⟨_, hD⟩ := c
  exact hD

lemma vert_card_eq_edge_card (c : G.IsCycle) : Fintype.card V = Fintype.card G.edgeSet := by
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

lemma three_le_card (c : G.IsCycle) : 3 ≤ Fintype.card V := by
  obtain ⟨hC, hD⟩ := c
  rw [connected_iff] at hC
  obtain ⟨_, hNE⟩ := hC
  obtain ⟨v⟩ := hNE
  have hNC : (G.neighborFinset v).card < Fintype.card V :=
    Finset.card_lt_univ_of_not_mem (G.not_mem_neighborFinset_self v)
  rw [G.card_neighborFinset_eq_degree, hD] at hNC
  simp [Nat.add_one_le_iff, hNC]

variable {v w : V}

lemma IsCycles (c : G.IsCycle) : G.IsCycles := by
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

-- lemma neighbor_nonempty (c : G.IsCycle) : Fintype.card (G.neighborSet v) > 0 := by
--   obtain ⟨_, hD⟩ := c
--   have hD : G.degree v = 2 := by apply hD
--   rw [card_neighborSet_eq_degree, hD]
--   trivial

lemma exists_adj (c : G.IsCycle) : ∃ (w : V), G.Adj v w := by
  obtain ⟨hC, hD⟩ := c
  have hD : G.degree v > 0 := by
    rw [hD]
    trivial
  simp [G.degree_pos_iff_exists_adj] at hD
  exact hD

-- lemma no_bridges (c : G.IsCycle) (h : G.Adj v w) : ¬G.IsBridge s(v, w) := by
--   have h1 : G.IsCycles := c.IsCycles
--   have h3 : (G.deleteEdges {s(v, w)}).Reachable v w := by
--     apply IsCycles.reachable_deleteEdges h h1
--   simp [isBridge_iff, h]
--   exact h3

-- lemma isCyclic (c : G.IsCycle) : ∃ (v : V) (p : G.Walk v v), p.IsCycle := by
--   have cCopy : G.IsCycle := c
--   obtain ⟨hC, _⟩ := cCopy
--   rw [connected_iff] at hC
--   obtain ⟨_, ⟨v⟩⟩ := hC
--   obtain ⟨w, hw⟩ := c.exists_adj
--   have h7 : (G \ fromEdgeSet {s(v, w)}).Reachable v w := by
--     apply IsCycles.reachable_deleteEdges hw c.IsCycles
--   have h8 : G.Adj v w ∧ (G \ fromEdgeSet {s(v, w)}).Reachable v w := by trivial
--   rw [adj_and_reachable_delete_edges_iff_exists_cycle] at h8
--   obtain ⟨u, p, ⟨hCyc, _⟩⟩ := h8
--   use u
--   use p

-- lemma notAcyclic (c : G.IsCycle) : ¬G.IsAcyclic := by
--   unfold IsAcyclic
--   simp
--   exact c.isCyclic

-- lemma notTree (c : G.IsCycle) : ¬G.IsTree := by simp [G.isTree_iff, c.notAcyclic]

lemma notTree (c : G.IsCycle) : ¬G.IsTree := by
  simp [G.isTree_iff_connected_and_card, c.vert_card_eq_edge_card]

lemma notAcyclic (c : G.IsCycle) : ¬G.IsAcyclic := by
  have hT : ¬G.IsTree := c.notTree
  obtain ⟨hC, _⟩ := c
  simp [G.isTree_iff, hC] at hT
  exact hT

lemma isCyclic (c : G.IsCycle) : ∃ (v : V) (p : G.Walk v v), p.IsCycle := by
  have hA : ¬G.IsAcyclic := c.notAcyclic
  unfold IsAcyclic at hA
  simp at hA
  exact hA

-- lemma oneCycle (c : G.IsCycle) (p : G.Walk v v) (h : p.IsCycle) :  := by
--   obtain ⟨w, hw⟩ := c.exists_adj
--   have h7 : (G \ fromEdgeSet {s(v, w)}).Reachable v w := by
--     apply IsCycles.reachable_deleteEdges hw c.IsCycles
--   have h8 : G.Adj v w ∧ (G \ fromEdgeSet {s(v, w)}).Reachable v w := by trivial
--   rw [adj_and_reachable_delete_edges_iff_exists_cycle] at h8
--   obtain ⟨u, p, ⟨hCyc, _⟩⟩ := h8
--   use u
--   use p
--   sorry

variable [DecidableEq V]

-- lemma isCyclic0 (c : G.IsCycle) : ∃ (v : V) (p : G.Walk v v), p.IsCycle := by
--   have h1 : G.IsCycles := c.IsCycles
--   obtain ⟨h1, h2, h3⟩ := c
--   obtain ⟨v⟩ := h1
--   have h4 : ∃ (w : V), G.Adj v w := by
--     have h5 : G.degree v = 2 := by apply h2
--     have h6 : G.degree v > 0 := by
--       rw [h5]
--       trivial
--     simp [G.degree_pos_iff_exists_adj] at h6
--     exact h6
--   obtain ⟨w, hw⟩ := h4
--   have h7 : (G \ fromEdgeSet {s(v, w)}).Reachable v w := by
--     apply IsCycles.reachable_deleteEdges hw h1
--   rw [reachable_delete_edges_iff_exists_walk] at h7
--   obtain ⟨p, hp⟩ := h7
--   have hp : s(v, w) ∉ p.reverse.edges := by
--     simp
--     exact hp
--   have h8 : s(v, w) ∉ p.reverse.bypass.edges := by
--     apply Set.not_mem_subset p.reverse.edges_bypass_subset
--     exact hp
--   have h11 : p.reverse.bypass.IsPath ∧ s(v, w) ∉ p.reverse.bypass.edges := by
--     have h10 : p.reverse.bypass.IsPath := p.reverse.bypass_isPath
--     trivial
--   rw [← p.reverse.bypass.cons_isCycle_iff hw] at h11
--   use v
--   use (cons hw p.reverse.bypass)



lemma isEulerian (c : G.IsCycle) : ∃ (v : V) (p : G.Walk v v), p.IsEulerian
    := by
  unfold IsEulerian
  sorry

lemma isHamiltonian (c : G.IsCycle) : G.IsHamiltonian := by
  unfold IsHamiltonian
  intro
  simp [isHamiltonianCycle_iff]
  obtain ⟨v, p, hp⟩ := c.isCyclic
  use v
  use p
  simp [hp]
  have h4 : p.tail.IsPath := by sorry
  rw [IsPath.isHamiltonian_iff h4]
  sorry

end IsCycle

end SimpleGraph
