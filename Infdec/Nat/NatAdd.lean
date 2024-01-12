import Infdec.Nat.Add

namespace wkmath
namespace Digits
theorem add''.closure{x:Digits}{d:Digit}(hx:x.isStdNat):(x.add'' d).isStdNat:=by{
  induction x generalizing d with
  | nil => cases d with
    | zero
    | one
    | two => simp[add'', isStdNat]
  | cons x' d' ih => {
    simp[add'']
    have h:=isStdNat.stdNat_heads hx
    cases h':add'' x' (d'.half_add3 d (0)).fst with
    | nil => {
      have ⟨hl, hr⟩ := not_ε h'
      rw[hl, isStdNat] at hx
      simp[head] at hx
      rw[isStdNat]
      simp[head]
      cases d' with
      | zero => contradiction
      | one => {
        cases d with
        | two => contradiction
        | zero
        | one => simp
      }
      | two => {
        cases d with
        | one
        | two => contradiction
        | zero => simp
      }
    }
    | cons y c => {
      apply isStdNat.not_ε_cons (y.cons c).noConfusion
      rw[←h']
      exact ih h
    }
  }
}

theorem add'.closure{x y:Digits}{d:Digit}(hx:x.isStdNat)(hy:y.isStdNat):(add' x y d).isStdNat:=by{
  match x, y with
  | nil, nil => {
    rw[add_ε]
    cases d with
    | zero
    | one
    | two => rw[add'',isStdNat];simp
  }
  | nil, cons _ _ => {
    rw[ε_add]
    exact add''.closure hy
  }
  | cons _ _, nil => {
    rw[add_ε]
    exact add''.closure hx
  }
  | cons xs xd, cons ys yd => {
    rw[add']
    rw[isStdNat]
    simp
    have hxs:=isStdNat.stdNat_heads hx
    have hys:=isStdNat.stdNat_heads hy
    cases h':(add' xs ys (Digit.half_add3 xd yd d).fst) with
    | nil => {
      have ⟨h0,h1,h2⟩:=not_ε h'
      simp[h0, isStdNat, head] at hx
      simp[h1, isStdNat, head] at hy
      match xd, yd, d with
      | (0), _, _
      | (1), (0), _
      | (2), (0), _
      | (1), (1), (1)
      | (1), (1), (2)
      | (1), (2), (0)
      | (1), (2), (1)
      | (1), (2), (2)
      | (2), (1), (0)
      | (2), (1), (1)
      | (2), (1), (2)
      | (2), (2), (0)
      | (2), (2), (1)
      | (2), (2), (2) => contradiction
      | (1), (1), (0) => simp
    }
    | cons zs zd => {
      simp[head]
      have h'':isStdNat (add' xs ys (Digit.half_add3 xd yd d).fst):=closure hxs hys
      rw[h'] at h''
      simp[isStdNat] at h''
      exact h''
    }
  }
}

theorem add.closure{x y:Digits}(hx:x.isStdNat)(hy:y.isStdNat):(x + y).isStdNat:=
  add'.closure hx hy

theorem add''.zero_add{x:Digits}{d:Digit}(h:x.isZero):x.add'' d =N (ε::d):=by{
  cases x with
  | nil => cases d with
    | zero
    | one
    | two => simp
  | cons xs xd => {
    rw[isZero] at h
    rw[h.right]
    cases d with
    | zero
    | one
    | two => {
      simp[add'', Digit.half_add3]
      simp[nat.eq]
      exact zero_nat_eq_zero h.left ε_isZero
    }
  }
}

theorem add''.congr{x y:Digits}{d:Digit}(h:x =N y):x.add'' d =N y.add'' d:=by{
  match x, y with
  | nil, nil => exact nat.eq.refl _
  | nil, cons _ _ => exact (zero_add ε_isZero).trans (zero_add (nat_eq_zero_isZero h ε_isZero)).symm
  | cons _ _, nil => exact (zero_add (nat_eq_zero_isZero h.symm ε_isZero)).trans (zero_add ε_isZero).symm
  | cons _ xd, cons _ yd => {
    rw[nat.eq] at h
    rw[h.right]
    simp[add'']
    rw[nat.eq]
    simp
    exact congr h.left
  }
}

theorem add'.add_zero{x y:Digits}{d:Digit}(h:y.isZero):add' x y d =N add'' x d:=by{
  induction y generalizing x d with
  | nil => rw[add_ε]; exact nat.eq.refl _
  | cons ys yd ih => {
    cases x with
    | nil => rw[ε_add]; exact add''.congr (zero_nat_eq_zero h ε_isZero)
    | cons xs xd => {
      simp[add',add'']
      rw[isZero] at h
      rw[h.right]
      rw[Digit.half_add3.comm23]
      rw[nat.eq]
      simp
      exact ih h.left
    }
  }
}

theorem add'.zero_add{x y:Digits}{d:Digit}(h:x.isZero):add' x y d =N add'' y d:=by{
  rw[add'.comm]
  exact add_zero h
}

theorem add'.congr{x y z w:Digits}{d:Digit}(h0:x =N z)(h1:y =N w):(add' x y d) =N (add' z w d):=by{
  match z, w with
  | _, nil => {
    have h1:=nat_eq_zero_isZero' h1 ε_isZero
    rw[add_ε]
    apply nat.eq.trans (add_zero h1)
    exact add''.congr h0
  }
  | nil, cons _ _ => {
    have h0:=nat_eq_zero_isZero' h0 ε_isZero
    rw[ε_add]
    apply nat.eq.trans (zero_add h0)
    exact add''.congr h1
  }
  | cons _ zd, cons _ wd => {
    apply nat.eq.symm
    match x, y with
    | _, nil => {
      have h1:=nat_eq_zero_isZero h1 ε_isZero
      rw[add_ε]
      apply nat.eq.trans (add_zero h1)
      exact add''.congr h0.symm
    }
    | nil, cons _ _ => {
      have h0:=nat_eq_zero_isZero h0 ε_isZero
      rw[ε_add]
      apply nat.eq.trans (zero_add h0)
      exact add''.congr h1.symm
    }
    | cons _ xd, cons _ yd => {
      rw[nat.eq] at h0 h1
      rw[h0.right,h1.right]
      simp[add',nat.eq]
      exact (congr h0.left h1.left).symm
    }
  }
}

theorem add.add_zero{x y:Digits}(h:y.isZero):(x.add y) =N x:=by{
  apply (add'.add_zero h).trans
  rw[add''.add_zero]
  exact nat.eq.refl _
}

theorem add.zero_add{x y:Digits}(h:x.isZero):(x.add y) =N y:=by{
  rw[comm]
  exact add_zero h
}

theorem add.comm'{x y:Digits}:(x.add y) =N (y.add x):=by{
  rw[comm]
  exact nat.eq.refl _
}

theorem add.congr{x y z w:Digits}(h0:x =N z)(h1:y =N w):(x.add y) =N (z.add w):=
  add'.congr h0 h1

theorem add''.nat_carry_cancel{x y:Digits}{d:Digit}(h:(x.add'' d) =N (y.add'' d)):x =N y:=by{
  match x, y with
  | nil, nil => exact nat.eq.refl _
  | nil, cons _ yd => {
    match yd, d with
    | _, (0) => simp[add_zero] at h; exact h
    | (0), (1)
    | (0), (2) => {
      simp[add'', Digit.half_add3] at h
      rw[nat.eq] at h
      have h:=h.left
      rw[nat.eq]
      simp[isZero]
      exact nat_eq_zero_isZero h ε_isZero
    }
    | (1), (1)
    | (1), (2)
    | (2), (1)
    | (2), (2) => {
      simp[add'', Digit.half_add3] at h
      rw[nat.eq] at h
      have h:=h.right
      contradiction
    }
  }
  | cons _ xd, nil => {
    match xd, d with
    | _, (0) => simp[add_zero] at h; exact h
    | (0), (1)
    | (0), (2) => {
      simp[add'', Digit.half_add3] at h
      rw[nat.eq] at h
      have h:=h.left
      rw[nat.eq]
      simp[isZero]
      exact nat_eq_zero_isZero' h ε_isZero
    }
    | (1), (1)
    | (1), (2)
    | (2), (1)
    | (2), (2) => {
      simp[add'', Digit.half_add3] at h
      rw[nat.eq] at h
      have h:=h.right
      contradiction
    }
  }
  | cons _ xd, cons _ yd => {
    rw[nat.eq]
    simp[add'', nat.eq] at h
    have ⟨hl, hr⟩:=h
    repeat rw[←Digit.digit_add] at hr
    have hr:=Digit.half_add3.snd_cancel hr
    simp[hr]
    rw[hr] at hl
    exact nat_carry_cancel hl
  }
}

theorem add''.cancel{x y:Digits}{c d:Digit}(h:(x.add'' c) =N (y.add'' d))(h':x =N y):c=d:=by{
  match x, y with
  | nil, nil => {
    have h:=(zero_add ε_isZero).symm.trans (h.trans (zero_add ε_isZero))
    exact h.right
  }
  | cons _ _, nil => {
    have h':=nat_eq_zero_isZero' h' ε_isZero
    have h:=(zero_add h').symm.trans (h.trans (zero_add ε_isZero))
    exact h.right
  }
  | nil, cons _ _ => {
    have h':=nat_eq_zero_isZero h' ε_isZero
    have h:=(zero_add ε_isZero).symm.trans (h.trans (zero_add h'))
    exact h.right
  }
  | cons _ xd, cons _ yd => {
    rw[nat.eq] at h'
    rw[h'.right] at h
    simp[add'', nat.eq] at h
    have h:=h.right
    repeat rw[←Digit.digit_add] at h
    exact Digit.half_add3.snd_cancel' h
  }
}

theorem add'.right_cancel{x y z w:Digits}{d:Digit}(h:(add' x y d) =N (add' z w d))(h':y =N w):x =N z:=by{
  match y, w with
  | nil, nil => {
    repeat rw[add_ε] at h
    exact add''.nat_carry_cancel h
  }
  | nil, cons _ _ => {
    have h:=h.trans (congr (nat.eq.refl z) h'.symm)
    repeat rw[add_ε] at h
    exact add''.nat_carry_cancel h
  }
  | cons _ _, nil => {
    have h:=(congr (nat.eq.refl x) h'.symm).trans h
    repeat rw[add_ε] at h
    exact add''.nat_carry_cancel h
  }
  | cons ys yd, cons ws wd => {
    have ih{x z:Digits}{c:Digit}(h:add' x ws c =N add' z ws c):x =N z:=right_cancel h (nat.eq.refl _)
    rw[nat.eq] at h'
    rw[h'.right] at h
    match x, z with
    | nil, nil => simp
    | nil, cons _ zd => {
      rw[ε_add] at h
      simp[add'',add', nat.eq] at h
      cases zd with
      | zero => {
        rw[Digit.half_add3.comm13] at h
        rw[Digit.half_add3.comm23] at h
        simp at h
        have h:=(add''.congr h'.left).symm.trans h
        simp[nat.eq,isZero]
        rw[←ε_add] at h
        have h:=ih h
        exact nat_eq_zero_isZero h ε_isZero
      }
      | one
      | two => {
        have h:=h.right
        rw[Digit.half_add3.comm12, Digit.half_add3.comm13] at h
        have h:=Digit.half_add3.snd_cancel h
        contradiction
      }
    }
    | cons _ xd, nil => {
      rw[ε_add] at h
      simp[add'', add', nat.eq] at h
      cases xd with
      | zero => {
        have h:=h.left
        have h:=h.trans (add''.congr h'.left.symm)
        rw[Digit.half_add3.comm13, Digit.half_add3.comm12] at h
        rw[←ε_add] at h
        have h:=(congr (nat.eq.refl _) h'.left.symm).trans (h.trans (congr (nat.eq.refl _) h'.left))
        have h:=ih h
        simp[nat.eq,isZero]
        exact nat_eq_zero_isZero' h ε_isZero
      }
      | one
      | two => {
        have h:=h.right
        repeat rw[←Digit.digit_add3] at h
        rw[Digit.half_add3.comm13,Digit.half_add3.comm12] at h
        have h:=Digit.half_add3.snd_cancel'' h
        contradiction
      }
    }
    | cons _ xd, cons _ zd => {
      simp[add'] at h
      rw[nat.eq] at h
      have ⟨hl, hr⟩:=h
      have hr:=Digit.half_add3.snd_cancel hr
      rw[hr]
      rw[hr] at hl
      have hl:=(congr (nat.eq.refl _) h'.left).symm.trans hl
      have hl:=ih hl
      simp[nat.eq]
      exact hl
    }
  }
}

theorem add'.left_cancel{x y z w:Digits}{d:Digit}(h:(add' x y d) =N (add' z w d))(h':x =N z):y =N w:=by{
  rw[comm] at h
  have h:=h.symm
  rw[comm] at h
  exact right_cancel h.symm h'
}

theorem add'.carry_cancel'{x y:Digits}{c d:Digit}(h:(add' x y c) =N (add' x y d)):c=d:=by{
  match x, y with
  | _, nil => {
    repeat rw[add_ε] at h
    exact add''.cancel h (nat.eq.refl _)
  }
  | nil, cons _ _ => {
    repeat rw[ε_add] at h
    exact add''.cancel h (nat.eq.refl _)
  }
  | cons _ xd, cons _ yd => {
    simp[add', nat.eq] at h
    have ⟨_, hr⟩:=h
    exact Digit.half_add3.snd_cancel'' hr
  }
}

theorem add'.carry_cancel{x y z w:Digits}{c d:Digit}(h:(add' x y c) =N (add' z w d))(h0:x =N z)(h1:y =N w):c=d:=by{
  have h1:=toStdNat_eq_of_nat_eq h1
  have h0:=toStdNat_eq_of_nat_eq h0
  have h:=(congr (toStdNat_nat_eq x) (toStdNat_nat_eq y)).trans (h.trans (congr (toStdNat_nat_eq z).symm (toStdNat_nat_eq w).symm))
  rw[h0,h1] at h
  exact carry_cancel' h
}

theorem add.right_cancel{x y z w:Digits}(h:(x.add y) =N (z.add w))(h':y =N w):x =N z:=
  add'.right_cancel h h'

theorem add.left_cancel{x y z w:Digits}(h:(x.add y) =N (z.add w))(h':x =N z):y =N w:=
  add'.left_cancel h h'

theorem add''.addone_notzero{x:Digits}:¬(x.add'' (1)).isZero:=by{
  induction x with
  | nil => simp[add'']
  | cons xs xd ih => {
    cases xd with
    | zero
    | one => {
      simp[add'', Digit.half_add3]
      simp[isZero]
    }
    | two => {
      simp[add'', Digit.half_add3]
      simp[isZero, ih]
    }
  }
}

theorem add''.notzero{x:Digits}{d:Digit}(h:(x.add'' d).isZero):x.isZero∧d=(0):=by{
  cases d with
  | zero => rw[add_zero] at h; simp[h]
  | one
  | two => {
    cases x with
    | nil => rw[add'', isZero] at h; exact h
    | cons _ xd => {
      cases xd with
      | zero
      | one
      | two => {
        simp[add'', Digit.half_add3, isZero, addone_notzero] at h
      }
    }
  }
}

theorem add''.notzero'{x:Digits}{d:Digit}(h:¬x.isZero):¬(x.add'' d).isZero:=by{
  intro h'
  apply h
  exact (notzero h').left
}

theorem add''.notzero''{x:Digits}{d:Digit}(h:d≠(0)):¬(x.add'' d).isZero:=by{
  intro h'
  apply h
  exact (notzero h').right
}

theorem add'.addone_notzero{x y:Digits}:¬(add' x y (1)).isZero:=by{
  match x, y with
  | _, nil => rw[add_ε]; exact add''.notzero'' (1).noConfusion
  | nil, cons _ _ => rw[ε_add]; exact add''.notzero'' (1).noConfusion
  | cons _ xd, cons _ yd => {
    match xd, yd with
    | (0), (0)
    | (0), (1)
    | (0), (2)
    | (1), (0)
    | (1), (1)
    | (1), (2)
    | (2), (0)
    | (2), (1)
    | (2), (2) => simp[add', Digit.half_add3, isZero, addone_notzero]
  }
}

theorem add'.addtwo_notzero{x y:Digits}:¬(add' x y (2)).isZero:=by{
  match x, y with
  | _, nil => rw[add_ε]; exact add''.notzero'' (2).noConfusion
  | nil, cons _ _ => rw[ε_add]; exact add''.notzero'' (2).noConfusion
  | cons _ xd, cons _ yd => {
    match xd, yd with
    | (0), (0)
    | (0), (1)
    | (0), (2)
    | (1), (0)
    | (1), (1)
    | (1), (2)
    | (2), (0)
    | (2), (1)
    | (2), (2) => simp[add', Digit.half_add3, isZero, addone_notzero, addtwo_notzero]
  }
}

theorem add.notzero{x y:Digits}(h:(x.add y).isZero):x.isZero ∧ y.isZero:=by{
  match x, y with
  | nil, nil => simp
  | nil, cons _ _ => rw[ε_add] at h;simp[h]
  | cons _ _, nil => rw[add_ε] at h;simp[h]
  | cons _ xd, cons _ yd => {
    simp[add, add'] at h
    match xd, yd with
    | (0), (1)
    | (0), (2)
    | (1), (0)
    | (1), (1)
    | (1), (2)
    | (2), (0)
    | (2), (1)
    | (2), (2) => {
      simp[isZero]
      simp[Digit.half_add3, isZero, add'.addone_notzero] at h
    }
    | (0), (0) => {
      simp[isZero]
      simp[Digit.half_add3, isZero, add'.addone_notzero] at h
      rw[←add] at h
      exact notzero h
    }
  }
}

theorem add.notzero'{x y:Digits}(h:¬x.isZero):¬(x.add y).isZero:=by{
  intro h'
  apply h
  simp[notzero h']
}

theorem add.notzero''{x y:Digits}(h:¬y.isZero):¬(x.add y).isZero:=by{
  intro h'
  apply h
  simp[notzero h']
}

theorem add'.notzero{x y:Digits}{d:Digit}(h:(add' x y d).isZero):x.isZero∧y.isZero∧d=(0):=by{
  match x, y with
  | _, nil => rw[add_ε] at h;simp[add''.notzero h]
  | nil, cons _ _ => rw[ε_add] at h;simp[add''.notzero h]
  | cons _ xd, cons _ yd => {
    match xd, yd, d with
    | (0), (0), (0) => {
      simp[isZero]
      simp[add', Digit.half_add3, isZero, addone_notzero, addtwo_notzero] at h
      rw[←add] at h
      exact add.notzero h
    }
    | (0), (0), (1)
    | (0), (0), (2)
    | (0), (1), (0)
    | (0), (1), (1)
    | (0), (1), (2)
    | (0), (2), (0)
    | (0), (2), (1)
    | (0), (2), (2)
    | (1), (0), (0)
    | (1), (0), (1)
    | (1), (0), (2)
    | (1), (1), (0)
    | (1), (1), (1)
    | (1), (1), (2)
    | (1), (2), (0)
    | (1), (2), (1)
    | (1), (2), (2)
    | (2), (0), (0)
    | (2), (0), (1)
    | (2), (0), (2)
    | (2), (1), (0)
    | (2), (1), (1)
    | (2), (1), (2)
    | (2), (2), (0)
    | (2), (2), (1)
    | (2), (2), (2) => {
      simp[isZero]
      simp[add', Digit.half_add3, isZero, addone_notzero, addtwo_notzero] at h
    }
  }
}

theorem add'.notzero'{x y:Digits}{d:Digit}(h:¬x.isZero):¬(add' x y d).isZero:=by{
  intro h'
  apply h
  simp[notzero h']
}

theorem add'.notzero''{x y:Digits}{d:Digit}(h:¬y.isZero):¬(add' x y d).isZero:=by{
  intro h'
  apply h
  simp[notzero h']
}

theorem add'.notzero'''{x y:Digits}{d:Digit}(h:d≠(0)):¬(add' x y d).isZero:=by{
  intro h'
  apply h
  simp[notzero h']
}

theorem add''.add_notzero_lt(x:Digits){d:Digit}(h:d ≠ (0)):x < x.add'' d:=by{
  match x with
  | ε => match d with | (0) | (1) | (2) => simp at *
  | x'::xd => {
    match xd, d with
    | (0), (0)
    | (1), (0)
    | (2), (0) => contradiction
    | (0), (1)
    | (0), (2)
    | (1), (1) => {
      simp[add'', Digit.half_add3, nat.lt]
      exact Or.inr (nat.eq.refl _)
    }
    | (1), (2)
    | (2), (1)
    | (2), (2) => {
      simp[add'', Digit.half_add3, nat.lt]
      exact add_notzero_lt _ (1).noConfusion
    }
  }
}

theorem add''.add_le(x:Digits)(d:Digit):x ≤ x.add'' d:=by{
  match x with
  | ε => match d with | (0) | (1) | (2) => simp
  | x'::xd => {
    match xd, d with
    | (0), (0)
    | (0), (1)
    | (0), (2)
    | (1), (0)
    | (1), (1)
    | (2), (0) => {
      simp[add'', Digit.half_add3, nat.le]
      exact Or.inr (nat.eq.refl _)
    }
    | (1), (2)
    | (2), (1)
    | (2), (2) => {
      simp[add'', Digit.half_add3, nat.le]
      exact add_notzero_lt _ (1).noConfusion
    }
  }
}
end Digits
end wkmath
