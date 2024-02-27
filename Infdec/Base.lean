theorem Or.comm{p q:Prop}(h:p ∨ q):q ∨ p:=by{
  cases h with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h
}

theorem Or.comm_iff(p q:Prop):p ∨ q ↔ q ∨ p:=
  Iff.intro Or.comm Or.comm

theorem Or.assoc{p q r:Prop}(h:(p ∨ q) ∨ r):p ∨ (q ∨ r):=
  h.elim (λ h' => h'.elim (λ p => Or.inl p) (λ q => Or.inr (Or.inl q))) (λ r => Or.inr (Or.inr r))

theorem Or.assoc'{p q r:Prop}(h:p ∨ (q ∨ r)):(p ∨ q) ∨ r:=
  h.elim (λ p => Or.inl (Or.inl p)) (λ h' => h'.elim (λ q => Or.inl (Or.inr q)) (λ r => Or.inr r))

theorem Or.assoc_iff(p q r:Prop):(p ∨ q) ∨ r ↔ p ∨ (q ∨ r):=
  Iff.intro assoc assoc'

theorem de_morgan_not_or{p q:Prop}:¬(p ∨ q)↔¬p∧¬q:=
  Iff.intro (λ h => And.intro (λ p => h (Or.inl p)) (λ q => h (Or.inr q))) (λ h h' => h'.elim (λ p => h.left p) (λ q => h.right q))

theorem de_morgan_not_and_of_or_not{p q:Prop}(h:¬p ∨ ¬q):¬(p ∧ q):=
  λ h' => h.elim (λ p => p h'.left) (λ q => q h'.right)

theorem de_morgan_not_and{p q:Prop}[Decidable p][Decidable q]:¬(p ∧ q) ↔ ¬p ∨ ¬q:=
  Decidable.not_and_iff_or_not p q

theorem not_not_iff{p:Prop}[Decidable p]:¬¬p↔p:=
  Iff.intro Decidable.of_not_not (λ p h => h p)

theorem a1i{p:Prop}(h:∀ _:Sort u, p):p:=by {
  exact h PEmpty
}

theorem ProdEq{α:Type u}{β:Type v}{x y:α × β}(h:x = y):x.fst = y.fst ∧ x.snd = y.snd :=
  ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem Nat.mul_ne_zero{x y:Nat}(h0:x ≠ 0)(h1:y ≠ 0):x * y ≠ 0:=by{
  match x, y with
  | x' + 1, y' + 1 => {
    simp[Nat.mul_add, Nat.add_mul]
    rw[←Nat.add_assoc]
    rw[Nat.add_one]
    simp
  }
}

theorem Nat.mul_eq_zero{x y:Nat}(h:x * y = 0):x = 0 ∨ y = 0:=by{
  match x, y with
  | 0, _ => exact Or.inl rfl
  | _ + 1, 0 => exact Or.inr rfl
  | _ + 1, _ + 1 => simp[Nat.add_mul, Nat.mul_add] at h; rw[←Nat.add_assoc, add_one] at h; contradiction
}

theorem Nat.add_eq_zero_iff{x y:Nat}:x + y = 0 ↔ x = 0 ∧ y = 0:=by{
  apply Iff.intro
  . {
    intro h
    match x, y with
    | 0, 0 => simp
    | _, _ + 1 => rw[←Nat.add_assoc, Nat.add_one] at h; contradiction
    | _ + 1, 0 => rw[Nat.add_one] at h; contradiction
  }
  . {
    intro h
    simp[h.left, h.right]
  }
}

theorem Nat.lt_asymm{x y:Nat}(h:x < y):¬y < x:=
  λ h' => Nat.lt_irrefl _ (Nat.lt_trans h h')

theorem Nat.lt_add_not_0(x:Nat){y:Nat}(h:y ≠ 0):x < x + y:=by{
  match y with
  | succ y => {
    rw[add_succ]
    exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (Nat.lt_succ_self _)
  }
}

theorem Nat.lt_not_0_add(x:Nat){y:Nat}(h:y ≠ 0):x < y + x:=by{
  rw[Nat.add_comm]
  exact lt_add_not_0 x h
}

theorem Nat.lt_iff_not_ge{x y:Nat}:x < y ↔ ¬y ≤ x:=
  Iff.intro (λ h h' => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt h' h)) (by{
    intro h
    induction x generalizing y with
    | zero => match y with
      | zero => contradiction
      | succ _ => exact Nat.zero_lt_succ _
    | succ x' ih => {
      match y with
      | zero => simp[Nat.zero_le] at h
      | succ y' => exact Nat.succ_lt_succ (ih (λ h' => h (succ_le_succ h')))
    }
  })

theorem Nat.divmod_unique{n:Nat}(x y:Nat){a b:Nat}(ha:a < n)(hb:b < n)(h:x * n + a = y * n + b):x = y ∧ a = b:=by{
  match n with
  | 0 => contradiction
  | n' + 1 => {
    match x, y with
    | 0, 0 => simp at *; exact h
    | 0, y' + 1 => {
      simp at h
      rw[Nat.add_mul] at h
      simp at h
      rw[Nat.add_right_comm] at h
      rw[h] at ha
      exact (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) ha)).elim
    }
    | x' + 1, 0 => {
      simp at h
      rw[Nat.add_mul] at h
      have h:=h.symm
      simp at h
      rw[Nat.add_right_comm] at h
      rw[h] at hb
      exact (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hb)).elim
    }
    | succ x', succ y' => {
      repeat rw[Nat.succ_mul] at h
      repeat rw[Nat.add_right_comm _ (n' + 1)] at h
      have h:=Nat.add_right_cancel h
      have h:=divmod_unique x' y' ha hb h
      simp[h.right, h.left]
    }
  }
}

theorem Nat.add_mono_cancel{x y z w:Nat}(h0:x + y ≤ z + w)(h1:w < y):x < z:=by{
  match y, w with
  | succ y', 0 => exact Nat.lt_of_lt_of_le (Nat.lt_add_not_0 x (Nat.noConfusion)) h0
  | succ y', succ w' => {
    repeat rw[add_succ] at h0
    have h0:=le_of_succ_le_succ h0
    have h1:=lt_of_succ_lt_succ h1
    exact add_mono_cancel h0 h1
  }
}

theorem Nat.lt_of_lt_add_right{x y z:Nat}(h:x + z < y + z):x < y:=by{
  induction z with
  | zero => simp at h; exact h
  | succ z ih => {
    simp[add_succ] at h
    exact ih (Nat.lt_of_succ_lt_succ h)
  }
}

theorem Nat.lt_of_lt_mul_right{x y z:Nat}(h:x * z < y * z):x < y:=by{
  match x, y with
  | 0, 0
  | succ x', 0 => simp[Nat.mul_zero, Nat.not_lt_zero] at h
  | 0, succ y' => exact Nat.zero_lt_succ _
  | succ x', succ y' => {
    apply Nat.succ_lt_succ
    repeat rw[Nat.succ_mul] at h
    have h:=Nat.lt_of_lt_add_right h
    exact lt_of_lt_mul_right h
  }
}

theorem Nat.le_iff_eq_or_lt{x y:Nat}:x ≤ y ↔ x = y ∨ x < y := by{
  apply Iff.intro
  intro h
  match x, y with
  | 0, 0 => exact Or.inl rfl
  | 0, succ y' => exact Or.inr (zero_lt_succ y')
  | succ x', 0 => contradiction
  | succ x', succ y' => {
    simp
    have h:=le_of_succ_le_succ h
    have h:=le_iff_eq_or_lt.mp h
    exact h.elim (λ h => Or.inl h) (λ h => Or.inr (Nat.succ_lt_succ h))
  }
  intro h
  exact h.elim (λ h => Nat.le_of_eq h) (λ h => Nat.le_of_lt h)
}

theorem Nat.lt_or_gt_of_ne{a b:Nat}(h:a ≠ b):a < b ∨ b < a :=by{
  have h0:=Nat.le_total a b
  simp[le_iff_eq_or_lt] at h0
  simp[h] at h0
  simp[h.symm] at h0
  exact h0
}

theorem Nat.ne_zero_iff_gt_zero{x:Nat}:x ≠ 0 ↔ 0 < x:=by{
  match x with
  | 0
  | succ n => simp[zero_lt_succ]
}

theorem Acc.prod_fst{α:Type u}{β:Type v}{r:α → α → Prop}{x:α}{y:β}(h:Acc r x):Acc (λ (a b:α × β) => r a.fst b.fst) (x, y):=by{
  have {x:α}{y y':β}(h:Acc (λ (a b:α × β) => r a.fst b.fst) (x, y)):Acc (λ (a b:α × β) => r a.fst b.fst) (x, y'):=by{
    apply Acc.intro
    intro ⟨x'',y''⟩ h'
    simp at h'
    have h'':r (x'', y'').fst (x, y).fst:=by simp[h']
    exact h.inv h''
  }
  apply h.ndrecOn
  intro x' _ ih
  apply Acc.intro
  simp
  intro ⟨x'',y''⟩
  have ih':=ih x''
  simp
  intro h'
  have ih'':=ih' h'
  exact this ih''
}

theorem Acc.prod_snd{α:Type u}{β:Type v}{r:β → β → Prop}{x:α}{y:β}(h:Acc r y):Acc (λ (a b:α × β) => r a.snd b.snd) (x, y):=by{
  have {x x':α}{y:β}(h:Acc (λ (a b:α × β) => r a.snd b.snd) (x, y)):Acc (λ (a b:α × β) => r a.snd b.snd) (x', y):=by{
    apply Acc.intro
    intro ⟨x'',y''⟩ h'
    simp at h'
    have h'':r (x'', y'').snd (x, y).snd:=by simp[h']
    exact h.inv h''
  }
  apply h.ndrecOn
  intro x' _ ih
  apply Acc.intro
  simp
  intro ⟨x'',y''⟩
  have ih':=ih y''
  simp
  intro h'
  have ih'':=ih' h'
  exact this ih''
}

theorem Acc.psigma_fst{α:Type u}{β:Type v}{r:α → α → Prop}{x:α}{y:β}(h:Acc r x):Acc (λ (a b:(_:α) ×' β) => r a.fst b.fst) {fst:=x, snd:=y}:=by{
  have {x:α}{y y':β}(h:Acc (λ (a b:(_:α) ×' β) => r a.fst b.fst) {fst:=x, snd:=y}):Acc (λ (a b:(_:α) ×' β) => r a.fst b.fst) {fst:=x, snd:=y'}:=by{
    apply Acc.intro
    intro ⟨x'',y''⟩ h'
    simp at h'
    have h'':r (x'', y'').fst (x, y).fst:=by simp[h']
    exact h.inv h''
  }
  apply h.ndrecOn
  intro x' _ ih
  apply Acc.intro
  simp
  intro ⟨x'',y''⟩
  have ih':=ih x''
  simp
  intro h'
  have ih'':=ih' h'
  exact this ih''
}

theorem Acc.psigma_snd{α:Type u}{β:Type v}{r:β → β → Prop}{x:α}{y:β}(h:Acc r y):Acc (λ (a b:(_:α) ×' β) => r a.snd b.snd) {fst:=x, snd:=y}:=by{
  have {x x':α}{y:β}(h:Acc (λ (a b:(_:α) ×' β) => r a.snd b.snd) {fst:=x, snd:=y}):Acc (λ (a b:(_:α) ×' β) => r a.snd b.snd) {fst:=x', snd:=y}:=by{
    apply Acc.intro
    intro ⟨x'',y''⟩ h'
    simp at h'
    have h'':r (x'', y'').snd (x, y).snd:=by simp[h']
    exact h.inv h''
  }
  apply h.ndrecOn
  intro x' _ ih
  apply Acc.intro
  simp
  intro ⟨x'',y''⟩
  have ih':=ih y''
  simp
  intro h'
  have ih'':=ih' h'
  exact this ih''
}

theorem WellFounded.prod_fst{α:Type u}{β:Type v}{r:α → α → Prop}(h:WellFounded r):WellFounded (λ (x y:α × β) => r x.fst y.fst):=
  WellFounded.intro (λ a => (h.apply a.fst).prod_fst)

theorem WellFounded.prod_snd{α:Type u}{β:Type v}{r:β → β → Prop}(h:WellFounded r):WellFounded (λ (x y:α × β) => r x.snd y.snd):=
  WellFounded.intro (λ a => (h.apply a.snd).prod_snd)

theorem WellFounded.psigma_fst{α:Type u}{β:Type v}{r:α → α → Prop}(h:WellFounded r):WellFounded (λ (x y:(_:α) ×' β) => r x.fst y.fst):=
  WellFounded.intro (λ a => (h.apply a.fst).psigma_fst)

theorem WellFounded.psigma_snd{α:Type u}{β:Type v}{r:β → β → Prop}(h:WellFounded r):WellFounded (λ (x y:(_:α) ×' β) => r x.snd y.snd):=
  WellFounded.intro (λ a => (h.apply a.snd).psigma_snd)

theorem WellFounded.func{α:Type u}{β:Type v}{f:α → β}{r:β → β → Prop}{x:α}(wf:WellFounded r):WellFounded (λ (a b:α) => r (f a) (f b)):=
  InvImage.wf f wf
