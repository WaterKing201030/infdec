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
theorem std_peano_3{x y:Digits}(hx:x.isStdNat)(hy:y.isStdNat)(h:x.Succ =N y.Succ):x = y:=
  isStdNat.unique hx hy (peano_3 h)
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
end Digits
end wkmath
