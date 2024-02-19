import Infdec.Nat.NatAddOrder
import Infdec.Nat.Sub
import Infdec.Nat.Mul

namespace wkmath
namespace Digits
def Zero:=ε
def One:=ε::(1)
def Succ(x:Digits):=x + One
def isPredOf(x y:Digits):=x.Succ =N y
theorem Zero_isStdNat:Zero.isStdNat:=by simp[isStdNat]
theorem Zero_is_zero:Zero.isZero:=by simp[isZero]
theorem One_isStdNat:One.isStdNat:=by simp[isStdNat]
theorem One_is_not_zero:¬One.isZero:=by simp[isZero]
theorem One_eq_Zero_Succ:One = Zero.Succ:=rfl
theorem add_One_eq_add''_one(x:Digits):x + One = add'' x (1):=by{
  rw[One]
  match x with
  | ε => simp[add.ε_add, add'']
  | xs::xd => {
    rw[add,add',add'']
    simp
  }
}
theorem not_zero_is_Succ{x:Digits}(h:¬x.isZero):∃(y:Digits), y.Succ = x:=by{
  match x with
  | ε => contradiction
  | xs::xd => {
    match xd with
    | (0) => {
      simp[isZero] at h
      have ⟨y,h⟩:=not_zero_is_Succ h
      apply Exists.intro (y::(2))
      simp[Succ, add_One_eq_add''_one, add'', Digit.half_add3]
      rw[←add_One_eq_add''_one, ←Succ]
      exact h
    }
    | (1) => {
      apply Exists.intro (xs::(0))
      simp[Succ, add_One_eq_add''_one,add'',Digit.half_add3]
    }
    | (2) => {
      apply Exists.intro (xs::(1))
      simp[Succ, add_One_eq_add''_one,add'',Digit.half_add3]
    }
  }
}

theorem zero_lt_Succ{x:Digits}(h:x.isZero)(y:Digits):x < y.Succ:=by{
  rw[Succ]
  exact nat.zero_lt_notzero h (add.notzero'' One_is_not_zero)
}

theorem ε_lt_Succ(x:Digits):ε < x.Succ:=
  zero_lt_Succ ε_isZero x

theorem succ_cancel{x y:Digits}(h:x.Succ =N y.Succ):x =N y:=
  nat.add_right_cancel h (nat.eq.refl _)

theorem strict_peano_add_2(x y:Digits):x + y.Succ = (x + y).Succ:=by{
  rw[Succ,Succ,←add.assoc]
}

theorem mul_One_nat_eq(x:Digits):x * One =N x:=by{
  rw[One]
  simp[mul, mul'.mul'_one_carry_zero]
  exact nat.zero_add (by simp)
}

theorem nat.le_iff_lt_Succ{x y:Digits}:x ≤ y ↔ x < y.Succ:=
  Iff.intro
    (λ h => nat.lt_of_lt_of_eq (nat.le_iff_lt_add''_one.mp h) (add_digit_nat_eq_add'' y (1)).symm)
    (λ h => nat.le_iff_lt_add''_one.mpr (nat.lt_of_lt_of_eq h (add_digit_nat_eq_add'' y (1))))

theorem nat.lt_iff_Succ_le{x y:Digits}:x < y ↔ x.Succ ≤ y:=
  Iff.intro
    (λ h => nat.le_of_eq_of_le (add_digit_nat_eq_add'' x (1)) (nat.lt_iff_add''_one_le.mp h))
    (λ h => nat.lt_iff_add''_one_le.mpr (nat.le_of_eq_of_le (add_digit_nat_eq_add'' x (1)).symm h))

theorem nat.lt_succ_self(x:Digits):x < x.Succ:=
  nat.add_right_not_zero_lt x One_is_not_zero

theorem nat.one_le_iff_not_zero(x:Digits):One ≤ x ↔ ¬x.isZero:=by{
  apply Iff.intro
  . exact λ h h' => (lt.irrefl x) (lt_of_lt_of_le (zero_lt_notzero h' One_is_not_zero) h)
  . {
    intro h
    rw[One_eq_Zero_Succ]
    rw[←lt_iff_Succ_le]
    exact zero_lt_notzero Zero_is_zero h
  }
}

/- WellFound Relation -/
section wf
def toOneBaseNat:Digits → Digits
  | ε => ε
  | xs::(0) => xs.toOneBaseNat.triple
  | xs::(1) => (xs.toOneBaseNat.triple::(0))
  | xs::(2) => ((xs.toOneBaseNat.triple::(0))::(0))

theorem toOneBaseNat_isZero(x:Digits):x.toOneBaseNat.isZero:=by{
  induction x with
  | nil => simp
  | cons xs xd ih => {
    match xd with
    | (0)
    | (1)
    | (2) => {
      repeat simp[isZero, toOneBaseNat]
      exact zero_triple_isZero ih
    }
  }
}

theorem zero_toOneBaseNat_is_ε{x:Digits}(h:x.isZero):x.toOneBaseNat = ε:=by{
  induction x with
  | nil => simp
  | cons xs xd ih => {
    simp[isZero] at h
    have ih:=ih h.left
    rw[h.right]
    rw[toOneBaseNat]
    rw[ih]
    rfl
  }
}

theorem toOneBaseNat_ε_isZero{x:Digits}(h:x.toOneBaseNat = ε):x.isZero:=by{
  induction x with
  | nil => simp
  | cons xs xd ih => {
    match xd with
    | (1)
    | (2) => simp[toOneBaseNat] at h
    | (0) => {
      simp[toOneBaseNat] at h
      simp[isZero]
      rw[←ε_triple] at h
      have h:=triple.cancel h
      exact ih h
    }
  }
}

theorem not_zero_toOneBaseNat_is_not_ε{x:Digits}(h:¬x.isZero):x.toOneBaseNat ≠ ε:=by{
  intro h'
  exact h (toOneBaseNat_ε_isZero h')
}

theorem toOneBaseNat_eq_of_nat_eq{x y:Digits}(h:x =N y):x.toOneBaseNat = y.toOneBaseNat:=by{
  apply isZero.len_unique (toOneBaseNat_isZero _) (toOneBaseNat_isZero _)
  match x, y with
  | _, ε => {
    have h:=nat_eq_zero_isZero' h ε_isZero
    rw[zero_toOneBaseNat_is_ε h]
    rw[zero_toOneBaseNat_is_ε ε_isZero]
    simp
  }
  | ε, _::_ => {
    have h:=nat_eq_zero_isZero h ε_isZero
    rw[zero_toOneBaseNat_is_ε h]
    rw[zero_toOneBaseNat_is_ε ε_isZero]
    simp
  }
  | xs::xd, ys::yd => {
    simp[nat.eq] at h
    rw[h.right]
    match yd with
    | (0)
    | (1)
    | (2) => {
      simp[toOneBaseNat, len.eq]
      have h:=toOneBaseNat_eq_of_nat_eq h.left
      rw[h]
      exact len.eq.refl _
    }
  }
}

theorem nat_eq_of_toOneBaseNat_eq{x y:Digits}(h:x.toOneBaseNat = y.toOneBaseNat):x =N y:=by{
  match x with
  | ε => {
    apply zero_nat_eq_zero ε_isZero
    simp[toOneBaseNat] at h
    exact toOneBaseNat_ε_isZero h.symm
  }
  | xs::xd => {
    match y with
    | ε => {
      simp[toOneBaseNat] at h
      exact toOneBaseNat_ε_isZero h
    }
    | ys::yd => {
      match xd, yd with
      | (0), (1)
      | (1), (2) => {
        simp[toOneBaseNat] at h
        have h:=(triple.mod1 _ _ _).elim (len.eq.from_strict_eq h)
        contradiction
      }
      | (1), (0)
      | (2), (1) => {
        simp[toOneBaseNat] at h
        have h:=(triple.mod1 _ _ _).elim (len.eq.from_strict_eq h.symm)
        contradiction
      }
      | (0), (2) => {
        simp[toOneBaseNat] at h
        have h:=(triple.mod2 _ _ _ _).elim (len.eq.from_strict_eq h)
        contradiction
      }
      | (2), (0) => {
        simp[toOneBaseNat] at h
        have h:=(triple.mod2 _ _ _ _).elim (len.eq.from_strict_eq h.symm)
        contradiction
      }
      | (0), (0)
      | (1), (1)
      | (2), (2) => {
        simp[nat.eq]
        simp[toOneBaseNat] at h
        have h:=triple.cancel h
        exact nat_eq_of_toOneBaseNat_eq h
      }
    }
  }
}

theorem Succ_toOneBaseNat_eq_toOneBaseNat_cons_zero(x:Digits):x.Succ.toOneBaseNat = x.toOneBaseNat::(0):=by{
  rw[Succ]
  match x with
  | ε => simp[toOneBaseNat]
  | xs::xd => {
    rw[One]
    match xd with
    | (0)
    | (1) => simp[add,add',Digit.half_add3,toOneBaseNat]
    | (2) => {
      simp[add,add',Digit.half_add3,toOneBaseNat]
      rw[←add_One_eq_add''_one,←Succ]
      rw[Succ_toOneBaseNat_eq_toOneBaseNat_cons_zero xs]
      exact triple_zero_cons_zero_eq_triple_zero_cons_three_zero (toOneBaseNat_isZero _)
    }
  }
}

theorem isPredOf.acc{x:Digits}:Acc isPredOf x:=by{
  apply Acc.intro
  intro y h
  rw[isPredOf] at h
  cases Decidable.em (x.isZero) with
  | inl h' => {
    rw[Succ] at h
    have h:=add.notzero'' One_is_not_zero (nat_eq_zero_isZero' h h')
    contradiction
  }
  | inr h' => {
    have : y.toOneBaseNat.isTails x.toOneBaseNat := by{
      rw[isTails]
      have : x.toOneBaseNat ≠ ε := not_zero_toOneBaseNat_is_not_ε h'
      simp[this]
      have : y.toStdNat.Succ = x.toStdNat := by{
        apply isStdNat.unique (add.closure (toStdNat_isStdNat y) One_isStdNat) (toStdNat_isStdNat x)
        apply nat.eq.symm
        apply nat.eq.trans (toStdNat_nat_eq x)
        apply nat.eq.trans h.symm
        rw[Succ]
        exact nat.eq_of_eq_add_eq (toStdNat_nat_eq y).symm (nat.eq.refl One)
      }
      have h:=toOneBaseNat_eq_of_nat_eq h
      rw[Succ_toOneBaseNat_eq_toOneBaseNat_cons_zero] at h
      have h:=h.symm
      rw[←zero_head_eq_zero_tail (toOneBaseNat_isZero y)] at h
      simp[h]
      rw[append.tails]
    }
    exact acc
  }
}
termination_by _ => x.toOneBaseNat

@[inline] instance isPredOf.instWF:WellFoundedRelation Digits:={
  rel:=isPredOf
  wf:=WellFounded.intro (fun (_:Digits) => acc)
}
end wf
/- all digits -/
/- peano_1 zero is Digit : prove by isZero definition -/
/- peano_2 succ is Digit : prove by + definition -/
theorem peano_3{x y:Digits}(h:x.Succ =N y.Succ):x =N y:=
  succ_cancel h
theorem peano_4(y:Digits){x:Digits}(h:x.isZero):y.Succ ≠N x:=
  nat.ne.intro (λ hn => add.notzero'' One_is_not_zero (nat_eq_zero_isZero' hn h))
theorem peano_5
  {P:Digits → Prop}
  (zero:∀(x:Digits),x.isZero → P x)
  (succ:∀(x:Digits),P x → P x.Succ)
  (x:Digits): P x := by{
    cases (nat.le_or_gt x ε) with
    | inl h => exact zero x (nat.le_ε_isZero h)
    | inr h => {
      have h:=nat.lt_not_zero h
      have ⟨y,h'⟩:=not_zero_is_Succ h
      have : y.isPredOf x := by simp[isPredOf]; rw[h']; exact nat.eq.refl x
      rw[←h']
      apply succ y
      exact peano_5 zero succ y
    }
  }
termination_by _ => x
/- peano add 0 : closure : proof by + definition -/
theorem peano_add_1(x:Digits){y:Digits}(h:y.isZero):x + y =N x:=
  nat.add_zero h
theorem peano_add_2(x y:Digits):x + y.Succ =N (x + y).Succ:=by
  rw[strict_peano_add_2]; exact nat.eq.refl _
theorem peano_le(x y:Digits):x ≤ y ↔ ∃(z:Digits), x + z =N y:=by{
  apply Iff.intro
  . {
    intro h
    apply Exists.intro (y.half_sub x)
    rw[add.comm]
    exact le_half_sub_add_cancel h
  }
  . {
    intro ⟨z,h⟩
    exact nat.le_of_le_of_eq (nat.add_right_le _ _) h
  }
}
theorem peano_le_ind_1(x:Digits):x ≤ x:=
  nat.le.refl x
theorem peano_le_ind_2{x y:Digits}(h:x ≤ y):x ≤ y.Succ:=
  h.trans (nat.add_right_le y One)
/- peano mul 0 : closure : proof by * definition -/
theorem peano_mul_1(x:Digits){y:Digits}(h:y.isZero):(x * y).isZero:=
  mul.mul_zero x h
theorem peano_mul_2(x y:Digits):x * y.Succ =N x * y + x:=
  (mul.right_distrib x y One).trans (nat.eq_of_eq_add_eq (nat.eq.refl (x * y)) (mul_One_nat_eq x))
/- std digits -/
theorem std_peano_1:Zero.isStdNat:=
  Zero_isStdNat
theorem std_peano_2{x:Digits}(h:x.isStdNat):x.Succ.isStdNat:=
  add.closure h One_isStdNat
theorem std_peano_3{x y:Digits}(hx:x.isStdNat)(hy:y.isStdNat)(h:x.Succ = y.Succ):x = y:=
  isStdNat.unique hx hy (peano_3 (by{rw[h]; exact nat.eq.refl _}))
theorem std_peano_4{x:Digits}(_:x.isStdNat):x.Succ ≠N Zero:=
  peano_4 x Zero_is_zero
theorem std_peano_5
  {P:Digits → Prop}
  {x:Digits}
  (zero:P Zero)
  (succ:∀(x:Digits),x.isStdNat → P x → P x.Succ)
  (h:x.isStdNat)
  : P x := by{
    cases (nat.le_or_gt x ε) with
    | inl h' => {
      have h':=nat.le_ε_isZero h'
      have h:=isStdNat_isZero_is_ε h h'
      rw[h]
      exact zero
    }
    | inr h' => {
      have h':=nat.lt_not_zero h'
      have ⟨y,h'⟩:=not_zero_is_Succ h'
      have h':y.toStdNat.Succ = x:=by{
        have h'':y.toStdNat.Succ.isStdNat:=std_peano_2 (toStdNat_isStdNat _)
        apply isStdNat.unique h'' h
        rw[←h']
        rw[Succ, Succ]
        exact nat.eq_of_eq_add_eq (toStdNat_nat_eq _) (nat.eq.refl _)
      }
      rw[←h']
      apply succ (toStdNat y) (toStdNat_isStdNat y)
      have : y.toStdNat.isPredOf x:=by simp[isPredOf]; rw[h']; exact nat.eq.refl x
      exact std_peano_5 zero succ (toStdNat_isStdNat y)
    }
  }
termination_by _ => x
theorem std_peano_add_0{x y:Digits}(hx:x.isStdNat)(hy:y.isStdNat):(x + y).isStdNat:=
  add.closure hx hy
theorem std_peano_add_1{x:Digits}(_:x.isStdNat):x + Zero = x:=
  add.add_ε x
theorem std_peano_add_2{x y:Digits}(_:x.isStdNat)(_:y.isStdNat):x + y.Succ = (x + y).Succ:=
  strict_peano_add_2 x y
theorem std_peano_le{x y:Digits}(hx:x.isStdNat)(hy:y.isStdNat):x ≤ y ↔ ∃(z:Digits), z.isStdNat ∧ x + z = y:=by{
  apply Iff.intro
  . {
    intro h
    apply Exists.intro (y.half_sub x).toStdNat
    apply And.intro
    . {
      exact toStdNat_isStdNat _
    }
    . {
      apply isStdNat.unique (add.closure hx (toStdNat_isStdNat _)) hy
      rw[add.comm]
      apply nat.eq.trans (nat.eq_of_eq_add_eq (toStdNat_nat_eq _) (nat.eq.refl _))
      exact le_half_sub_add_cancel h
    }
  }
  . {
    intro ⟨z,h⟩
    rw[←h.right]
    exact nat.add_right_le x z
  }
}
theorem std_peano_le_ind_1{x:Digits}(_:x.isStdNat):x ≤ x:=
  peano_le_ind_1 x
theorem std_peano_le_ind_2{x y:Digits}(_:x.isStdNat)(_:y.isStdNat)(h:x ≤ y):x ≤ y.Succ:=
  peano_le_ind_2 h
theorem std_peano_mul_0{x y:Digits}(hx:x.isStdNat)(hy:y.isStdNat):(x *ₛ y).isStdNat:=
  std_mul.closure hx hy
theorem std_peano_mul_1{x:Digits}(_:x.isStdNat):x *ₛ Zero = Zero:=by
  simp[std_mul, mul]
theorem std_peano_mul_2{x y:Digits}(hx:x.isStdNat)(hy:y.isStdNat):x *ₛ y.Succ = x *ₛ y + x:=by{
  apply isStdNat.unique (std_peano_mul_0 hx (std_peano_2 hy)) (std_peano_add_0 (std_peano_mul_0 hx hy) hx)
  repeat rw[std_mul]
  exact ((toStdNat_nat_eq _).trans (peano_mul_2 _ _)).trans (nat.eq_of_eq_add_eq (toStdNat_nat_eq _).symm (nat.eq.refl _))
}

section lt_wf

theorem nat.lt.acc_eq{x y:Digits}(hn:x =N y)(ha:Acc nat.lt x):Acc nat.lt y:=
  Acc.intro y (λ _ h => ha.inv (nat.lt_of_lt_of_eq h hn.symm))

theorem nat.lt.acc{x:Digits}:Acc nat.lt x:=
  peano_5
    (λ _ h => Acc.intro _ (λ _ h' => (nat.lt_not_zero h' h).elim))
    (λ _ ih => Acc.intro _ (λ _ h => (le_iff_lt_Succ.mpr h).to_eq_or_lt.elim (λ h => acc_eq h.symm ih) ih.inv))
    _

@[inline] instance nat.lt.wf:WellFounded lt:=
  WellFounded.intro (λ _ => acc)

@[inline] instance nat.lt.instWF:WellFoundedRelation Digits:=
  ⟨lt, wf⟩
end lt_wf

def toNat:Digits → Nat
  | ε => 0
  | x::d => x.toNat * 3 + d.toNat

theorem isZero_iff_toNat_eq_zero{x:Digits}:x.isZero ↔ x.toNat = 0:=by{
  apply Iff.intro
  . {
    intro h
    induction x with
    | nil => simp
    | cons _ _ ih => {
      rw[isZero] at h
      simp[h.right] at *
      simp[toNat, Digit.toNat]
      rw[ih h]
    }
  }
  . {
    intro h
    induction x with
    | nil => simp
    | cons _ d ih => {
      rw[isZero]
      rw[toNat] at h
      rw[Nat.add_eq_zero_iff] at h
      match d with
      | (1) | (2) => simp at h
      | (0) => {
        simp
        apply ih
        have h:=Nat.mul_eq_zero h.left
        simp at h
        exact h
      }
    }
  }
}

theorem nat_eq_iff_toNat_eq{x y:Digits}:x =N y ↔ x.toNat = y.toNat:=by{
  apply Iff.intro
  . {
    intro h
    match x, y with
    | ε, ε => rfl
    | ε, _::_
    | _::_, ε => rw[nat.eq] at h; rw[isZero_iff_toNat_eq_zero] at h; rw[h]; rfl
    | _::_, _::_ => {
      rw[nat.eq] at h
      rw[h.right]
      rw[toNat, toNat]
      have h:=nat_eq_iff_toNat_eq.mp h.left
      rw[h]
    }
  }
  . {
    intro h
    match x, y with
    | ε, ε => exact nat.eq.refl _
    | ε, _::_ => {
      rw[toNat] at h
      have h:=h.symm
      rw[←isZero_iff_toNat_eq_zero] at h
      exact zero_nat_eq_zero ε_isZero h
    }
    | _::_, ε => {
      rw[toNat] at h
      rw[←isZero_iff_toNat_eq_zero] at h
      exact zero_nat_eq_zero h ε_isZero
    }
    | x'::xd, y'::yd => {
      rw[nat.eq]
      rw[toNat, toNat] at h
      have h:=Nat.divmod_unique _ _ Digit.toNat_lt_3 Digit.toNat_lt_3 h
      rw[←Digit.eq_iff_toNat_eq] at h
      exact ⟨nat_eq_iff_toNat_eq.mpr h.left,h.right⟩
    }
  }
}

theorem succ_toNat_eq_toNat_succ{x:Digits}:x.Succ.toNat = x.toNat.succ:=by{
  rw[Succ, One]
  match x with
  | ε => simp
  | x'::xd => {
    match xd with
    | (0) | (1) => simp[add,add', Digit.half_add3, toNat, Digit.toNat]
    | (2) => {
      simp[add, add', Digit.half_add3]
      rw[←add_One_eq_add''_one, ←Succ]
      simp[toNat, Digit.toNat]
      rw[Nat.succ_eq_add_one]
      rw[Nat.add_assoc]
      have : 2 + 1 = 3 := by simp
      rw[this]
      rw[←Nat.succ_mul]
      rw[succ_toNat_eq_toNat_succ]
    }
  }
}

theorem add_toNat_eq_toNat_add{x y:Digits}:(x + y).toNat = x.toNat + y.toNat:=by{
  induction y using peano_5 with
  | zero y h => {
    rw[nat_eq_iff_toNat_eq.mp (nat.add_zero h)]
    rw[isZero_iff_toNat_eq_zero.mp h]
    simp
  }
  | succ y ih => {
    rw[strict_peano_add_2, succ_toNat_eq_toNat_succ, ih, succ_toNat_eq_toNat_succ, Nat.add_succ]
  }
}

theorem mul_toNat_eq_toNat_mul{x y:Digits}:(x * y).toNat = x.toNat * y.toNat:=by{
  induction y using peano_5 with
  | zero y h => {
    rw[nat_eq_iff_toNat_eq.mp (zero_nat_eq_zero (peano_mul_1 _ h) ε_isZero)]
    rw[isZero_iff_toNat_eq_zero.mp h]
    simp
  }
  | succ y ih => {
    rw[nat_eq_iff_toNat_eq.mp (peano_mul_2 _ _), add_toNat_eq_toNat_add]
    rw[succ_toNat_eq_toNat_succ, Nat.mul_succ, ih]
  }
}

theorem toNat_lt_of_lt{x y:Digits}(h:x < y):x.toNat < y.toNat:=by{
  match x, y with
  | ε, ε
  | _::_, ε => contradiction
  | ε, _::_ => {
    simp[nat.lt] at h
    rw[toNat]
    rw[isZero_iff_toNat_eq_zero] at h
    exact Nat.zero_lt_of_ne_zero h
  }
  | x'::xd, y'::yd => {
    simp[nat.lt] at h
    cases h with
    | inl h => {
      rw[toNat, toNat]
      apply Nat.lt_of_lt_of_le (Nat.add_lt_add_left Digit.toNat_lt_3 _)
      apply λ h => Nat.le_trans h (Nat.le_add_right _ _)
      rw[←Nat.succ_mul]
      apply Nat.mul_le_mul_right
      apply Nat.succ_le_of_lt
      exact toNat_lt_of_lt h
    }
    | inr h => {
      rw[toNat, toNat]
      rw[nat_eq_iff_toNat_eq.mp h.right]
      exact Nat.add_lt_add_left (Digit.lt_iff_toNat_lt.mp h.left) _
    }
  }
}

theorem lt_of_toNat_lt{x y:Digits}(h:x.toNat < y.toNat):x < y:=by{
  match x, y with
  | ε, ε
  | _::_, ε => contradiction
  | ε, _::_ => {
    simp[nat.lt]
    have h:=Nat.not_eq_zero_of_lt h
    rw[isZero_iff_toNat_eq_zero]
    exact h
  }
  | x'::xd, y'::yd => {
    simp[nat.lt]
    rw[toNat, toNat] at h
    cases nat.trichotomous x' y' with
    | inl h' => exact Or.inl h'
    | inr h' => cases h' with
      | inl h' => {
        rw[nat_eq_iff_toNat_eq.mp h'] at h
        repeat rw[Nat.add_comm (y'.toNat * 3)] at h
        have h:=Nat.lt_of_lt_add_right h
        exact Or.inr ⟨Digit.lt_iff_toNat_lt.mpr h,h'⟩
      }
      | inr h' => {
        have h':=toNat_lt_of_lt h'
        have h:Nat.mul x'.toNat 3 < y'.toNat * 3 + 3:=Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h) (Nat.add_lt_add_left Digit.toNat_lt_3 _)
        rw[←Nat.succ_mul] at h
        have h:=Nat.lt_of_lt_mul_right h
        have h:=Nat.le_of_lt_succ h
        exact (Nat.not_le_of_gt h' h).elim
      }
  }
}

theorem lt_iff_toNat_lt{x y:Digits}:x < y ↔ x.toNat < y.toNat:=
  ⟨toNat_lt_of_lt,lt_of_toNat_lt⟩

theorem le_iff_toNat_le{x y:Digits}:x ≤ y ↔ x.toNat ≤ y.toNat:=by{
  rw[nat.le_iff_eq_or_lt]
  rw[nat_eq_iff_toNat_eq]
  rw[lt_iff_toNat_lt]
  exact Nat.le_iff_eq_or_lt.symm
}
end Digits
end wkmath
