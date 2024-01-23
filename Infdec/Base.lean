theorem Or.comm{p q:Prop}(h:p ∨ q):q ∨ p:=by{
  cases h with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h
}

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
