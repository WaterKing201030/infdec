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
