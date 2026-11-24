import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4265

open PEqualNP.CircuitLowerBounds

-- one evaluation step of a circuit
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma getD_step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  unfold step
  rw [List.getD_append _ _ _ _ h]

lemma getD_foldl_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (step w g) (by unfold step; simp; omega), getD_step_lt w g i h]

lemma forall2_mem_right {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) {b : β} (hb : b ∈ l2) : ∃ a ∈ l1, R a b := by
  induction h with
  | nil => simp at hb
  | cons hab _ ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨a, ha, hr⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

lemma forall2_mem_left {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) {a : α} (ha : a ∈ l1) : ∃ b ∈ l2, R a b := by
  induction h with
  | nil => simp at ha
  | cons hab _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨b, hb, hr⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

lemma length_foldl (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons,
      List.length_nil]
    omega

lemma main (x3 x4 : ℕ) (x5 : Fin 7) (x6 : Fin 7 → Bool) :
    ∀ (g1s g2s : List Gate),
    List.Forall₂ (fun (x8 x9 : Gate) => x8.op = x9.op ∧ List.Forall₂
      (fun (x10 x11 : ℕ) => x11 = x10 + 1 ∨ x11 = 0 ∧ (x10 = x3 ∨ x10 = x4))
      x8.inputs x9.inputs) g1s g2s →
    (∀ x10 ∈ g1s, (x5 : ℕ) ∈ x10.inputs → x10.op = GateOp.or ∧
      ∃ x13 : Fin 7, x13 ≠ x5 ∧ (x13 : ℕ) ∈ x10.inputs ∧ x6 x13 = true) →
    ∀ (w w' : List Bool), w.length = w'.length → 8 ≤ w.length →
    w.getD 0 false = true →
    (∀ k : Fin 7, k ≠ x5 → w.getD ((k : ℕ) + 1) false = x6 k) →
    (∀ i, i ≠ (x5 : ℕ) + 1 → w.getD i false = w'.getD i false) →
    ∀ i, i ≠ (x5 : ℕ) + 1 → (g2s.foldl step w).getD i false = (g2s.foldl step w').getD i false := by
  intro g1s g2s hF
  induction hF with
  | nil =>
    intro _ w w' _ _ _ _ heq i hi
    exact heq i hi
  | @cons g1 g2 g1s g2s hg _ ih =>
    intro hor w w' hlen h8 h0 hk heq
    obtain ⟨hop, hin⟩ := hg
    -- the new gate takes the same value on both sides
    have hval : g2.op.eval (g2.inputs.map fun i => w.getD i false) =
        g2.op.eval (g2.inputs.map fun i => w'.getD i false) := by
      by_cases hm : (x5 : ℕ) + 1 ∈ g2.inputs
      · obtain ⟨a, ha, hra⟩ := forall2_mem_right hin hm
        have ha5 : a = (x5 : ℕ) := by
          rcases hra with h | ⟨h, _⟩
          · omega
          · omega
        subst ha5
        obtain ⟨hor1, x13, hne, hx13, htrue⟩ := hor g1 (List.mem_cons_self ..) ha
        obtain ⟨b, hb, hrb⟩ := forall2_mem_left hin hx13
        have hbw : w.getD b false = true := by
          rcases hrb with h | ⟨h, _⟩
          · subst h
            rw [hk x13 hne, htrue]
          · subst h
            exact h0
        have hbne : b ≠ (x5 : ℕ) + 1 := by
          rcases hrb with h | ⟨h, _⟩
          · subst h
            intro h'
            apply hne
            ext
            omega
          · omega
        have hbw' : w'.getD b false = true := by
          rw [← heq b hbne]
          exact hbw
        rw [← hop, hor1]
        show (List.map _ _).any id = (List.map _ _).any id
        rw [List.any_eq_true.2 ⟨w.getD b false, List.mem_map.2 ⟨b, hb, rfl⟩, hbw⟩,
          List.any_eq_true.2 ⟨w'.getD b false, List.mem_map.2 ⟨b, hb, rfl⟩, hbw'⟩]
      · congr 1
        apply List.map_congr_left
        intro i hi
        apply heq
        intro h
        exact hm (h ▸ hi)
    simp only [List.foldl_cons]
    apply ih (fun x hx hx5 => hor x (List.mem_cons_of_mem _ hx) hx5)
    · simp [step, hlen]
    · simp [step]
      omega
    · rw [getD_step_lt _ _ _ (by omega)]
      exact h0
    · intro k hk'
      rw [getD_step_lt _ _ _ (by omega)]
      exact hk k hk'
    · intro i hi
      unfold step
      by_cases hlt : i < w.length
      · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
        exact heq i hi
      · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), hlen, hval]

end PEqualNP.Outside.L_meta_4265

theorem PEqualNP.Outside.L_meta_4265 : ∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) (x5 : Fin (7 : ℕ)) (x6 x7 : Fin (7 : ℕ) → Bool), List.Forall₂ (fun (x8 x9 : PEqualNP.CircuitLowerBounds.Gate) => x8.op = x9.op ∧ List.Forall₂ (fun (x10 x11 : ℕ) => x11 = x10 + (1 : ℕ) ∨ x11 = (0 : ℕ) ∧ (x10 = x3 ∨ x10 = x4)) x8.inputs x9.inputs) x1.gates x2.gates → (∀ (x9 : Fin (7 : ℕ)), x9 ≠ x5 → x6 x9 = x7 x9) → (∀ x10 ∈ x1.gates, ↑x5 ∈ x10.inputs → x10.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ (x13 : Fin (7 : ℕ)), x13 ≠ x5 ∧ ↑x13 ∈ x10.inputs ∧ x6 x13 = Bool.true) → x1.output ≠ ↑x5 → (x2.wires (Bool.true :: List.ofFn x6)).getD (x1.output + (1 : ℕ)) Bool.false = (x2.wires (Bool.true :: List.ofFn x7)).getD (x1.output + (1 : ℕ)) Bool.false := by
  intro x1 x2 x3 x4 x5 x6 x7 hF hagree hor hout
  rw [PEqualNP.Outside.L_meta_4265.wires_eq, PEqualNP.Outside.L_meta_4265.wires_eq]
  apply PEqualNP.Outside.L_meta_4265.main x3 x4 x5 x6 x1.gates x2.gates hF hor
  · simp
  · simp
  · rfl
  · intro k _
    fin_cases k <;> rfl
  · intro i hi
    rcases i with _ | i
    · rfl
    · rw [List.getD_cons_succ, List.getD_cons_succ]
      by_cases h7 : i < 7
      · have hne : (⟨i, h7⟩ : Fin 7) ≠ x5 := by
          intro h
          apply hi
          rw [← h]
        rw [List.getD_eq_getElem _ _ (by simpa using h7),
          List.getD_eq_getElem _ _ (by simpa using h7), List.getElem_ofFn, List.getElem_ofFn]
        exact hagree _ hne
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  · intro h
    apply hout
    omega
