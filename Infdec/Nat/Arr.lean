import Infdec.Digits
import Infdec.Nat.Length

namespace wkmath
namespace digitsArr
def sum:digitsArr → Digits
  | δ => ε
  | a::d => a.sum + d
end digitsArr

namespace Digits
theorem cutTails_padtailzero_add_getTails_nat_eq(x y:Digits):(cutTails x y ++ y.toZero) + getTails x y =N x:=by{
  induction y generalizing x with
  | nil => {
    match x with | ε | _::_ => simp[cutTails, toZero, getTails, nat.eq.refl]
  }
  | cons y' yd ih => {
    match x with
    | ε => {
      simp[cutTails, getTails]
      exact zero_nat_eq_zero (toZero_isZero _) ε_isZero
    }
    | x'::xd => {
      match xd with | (0) | (1) | (2) => {
        rw[cutTails, toZero, getTails, append, add, add']
        simp[Digit.half_add3]
        simp[nat.eq]
        rw[←add]
        exact ih x'
      }
    }
  }
}

theorem padtailzero_le(x:Digits){y:Digits}(h:y.isZero):x ≤ x ++ y:=by{
  induction y with
  | nil => simp[nat.le.refl]
  | cons y' yd ih => {
    rw[isZero] at h
    rw[h.right]
    match x with
    | ε => exact nat.ε_le _
    | x'::xd => {
      rw[append]
      simp[nat.le]
      cases Decidable.em (x'.isZero) with
      | inl h' => {
        match xd with
        | (0) => {
          apply Or.inr
          simp
          apply zero_nat_eq_zero h'
          apply λ h'' => zero_append_zero_isZero h'' h.left
          simp[isZero]
          exact h'
        }
        | (1)
        | (2) => {
          apply Or.inl
          apply nat.zero_lt_notzero h'
          have ih:=ih h.left
          intro h''
          have ih:=nat.le_zero_isZero ih h''
          simp[isZero] at ih
        }
      }
      | inr h' => {
        apply Or.inl
        have ih:=ih h.left
        apply λ h => nat.lt_of_lt_of_le h ih
        exact nat.not_zero_lt_cons h' xd
      }
    }
  }
}

theorem not_zero_padtailzero_not_ε_lt{x y:Digits}(h0:¬x.isZero)(h1:y.isZero)(h2:y ≠ ε):x < x ++ y:=by{
  induction y generalizing x with
  | nil => contradiction
  | cons y' yd ih => {
    rw[isZero] at h1
    have ih:=ih h0 h1.left
    cases y' with
    | nil => simp[append]; exact nat.not_zero_lt_cons h0 _
    | cons y'' yd' => {
      simp[isZero] at *
      simp[h1.left.right, h1.right] at *
      apply ih.trans
      repeat rw[append]
      simp[nat.lt]
      apply nat.not_zero_lt_cons
      exact not_zero_append_isNotZero h0
    }
  }
}

theorem cutTails_add_getTails_le(x y:Digits):cutTails x y + getTails x y ≤ x:=by{
  have h:cutTails x y + getTails x y ≤ (cutTails x y ++ y.toZero) + getTails x y:=
    nat.le_of_add_left_le (padtailzero_le _ (toZero_isZero _)) _
  exact nat.le_of_le_of_eq h (cutTails_padtailzero_add_getTails_nat_eq _ _)
}

theorem cutTails_not_ε_not_zero_add_getTails_lt{x y:Digits}(h0:y ≠ ε)(h1:¬(cutTails x y).isZero):cutTails x y + getTails x y < x:=by{
  apply λ h => nat.lt_of_lt_of_eq h (cutTails_padtailzero_add_getTails_nat_eq x y)
  apply λ h => nat.lt_of_add_left_lt
  exact not_zero_padtailzero_not_ε_lt h1 (toZero_isZero y) (by{intro h; apply h0; match y with | ε => rfl | _::_ => rw[toZero] at h; contradiction})
}

theorem slice_sum_le(x:Digits){y:Digits}(h:y ≠ ε):(x.slice h).sum ≤ x:=by{
  rw[slice]
  cases Decidable.em (x ≤L y) with
  | inl h' => {
    simp[h']
    repeat rw[digitsArr.sum]
    rw[add.ε_add]
    exact nat.le.refl _
  }
  | inr h' => {
    simp[h']
    rw[digitsArr.sum]
    apply λ h => nat.le.trans h (cutTails_add_getTails_le x y)
    apply λ h => nat.le_of_add_left_le h (getTails x y)
    have : x.cutTails y <L x:=by{
      cases x with
      | nil => match y with | _::_ => simp[len.le] at h'
      | cons x' d' => {
        simp[cutTails, len.lt, len.le] at *
        match y with | _::_ => {
          simp[cutTails]
          exact len.lt_of_le_of_lt (cutTails_len_le _ _) (len.lt_cons x' d')
        }
      }
    }
    exact slice_sum_le _ h
  }
}
termination_by' {
  rel:=λ x y => x.fst <L y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) len.lt.wf
}

theorem slice_cutTails_not_zero_sum_lt{x y:Digits}(h0:y ≠ ε)(h1:¬(cutTails x y).isZero):(x.slice h0).sum < x:=by{
  rw[slice]
  cases Decidable.em (x ≤L y) with
  | inl h => {
    rw[len_le_cutTails_eq_ε h] at h1
    contradiction
  }
  | inr h => {
    simp[h, digitsArr.sum]
    apply λ h => nat.lt_of_le_of_lt h (cutTails_not_ε_not_zero_add_getTails_lt h0 h1)
    apply nat.le_of_add_left_le
    exact slice_sum_le _ h0
  }
}

theorem padtailzero_nat_eq_mul_one_pad_zero(x:Digits){y:Digits}(h:y.isZero):x ++ y =N x * (ε::(1) ++ y):=by{
  induction y with
  | nil => simp; exact (mul_One_nat_eq x).symm
  | cons y' d ih => {
    rw[isZero] at h
    rw[h.right]
    rw[append]
    have ih:=ih h.left
    rw[append, mul]
    rw[mul'.mul'_zero_carry_zero]
    apply λ h => nat.eq.trans h (nat.add_zero (toZero_isZero x)).symm
    simp[nat.eq]
    exact ih
  }
}

theorem replace_eq_mul_one_zero_cycle(x y:Digits):x.replace y =N y * (x.replace (y.toZero + (ε::(1)))):=by{
  match x with
  | ε => simp[replace]; exact zero_nat_eq_zero ε_isZero (mul.mul_zero y ε_isZero)
  | x'::d => {
    rw[replace, replace]
    have h1:=cutTails_padtailzero_add_getTails_nat_eq (x'.replace y ++ y) y
    simp[append_cutTails_cancel, append_getTails] at h1
    apply h1.symm.trans
    apply nat.eq.symm
    have h2:=mul.left_congr y (cutTails_padtailzero_add_getTails_nat_eq (x'.replace (y.toZero + ε::(1)) ++ (y.toZero + ε::(1))) (y.toZero + ε::(1)))
    simp[append_cutTails_cancel, append_getTails] at h2
    apply h2.symm.trans
    apply (mul.right_distrib _ _ _).trans
    have h3:y * (toZero y + ε :: (1) ) =N y:=by{
      apply (mul.right_distrib _ _ _).trans
      apply (nat.zero_add (mul.mul_zero _ (toZero_isZero _))).trans
      exact mul_One_nat_eq _
    }
    apply λ h => nat.eq_of_eq_add_eq h h3
    have h4:=replace_eq_mul_one_zero_cycle x' y
    match y with
    | ε => {
      apply (zero_nat_eq_zero (mul.zero_mul ε_isZero _) ε_isZero).trans
      simp[replace_ε, toZero]
    }
    | y'::d' => {
      simp[toZero]
      simp[add, add', add'', Digit.half_add3]
      simp[toZero.idemp]
      have h5:(y'.toZero::(0)).isZero:=by simp[isZero]; exact toZero_isZero _
      apply (mul.left_congr (y'::d') (padtailzero_nat_eq_mul_one_pad_zero _ h5)).trans
      apply (mul.assoc _ _ _).symm.trans
      apply nat.eq.symm
      apply (padtailzero_nat_eq_mul_one_pad_zero _ h5).trans
      apply mul.right_congr
      simp[add, add', add'', Digit.half_add3] at h4
      exact h4
    }
  }
}

theorem toNegOne_add_One_eq_one_pad_zero(x:Digits):x.toNegOne + One = ε::(1) ++ x.toZero:=by{
  match x with
  | ε => {
    simp[toNegOne, toZero]
    rfl
  }
  | x'::d => {
    simp[toNegOne, toZero, One]
    simp[add, add', Digit.half_add3, append]
    rw[←add_One_eq_add''_one]
    exact toNegOne_add_One_eq_one_pad_zero x'
  }
}

theorem one_pad_zero_mul_two_nat_eq_two_pad_zero{x:Digits}(h:x.isZero):(ε::(1) ++ x) * (ε::(2)) =N ε::(2) ++ x:=by{
  induction x with
  | nil => simp
  | cons _ _ ih => {
    simp[isZero] at h
    have ih:=ih h.left
    simp[append, h.right]
    simp[mul, mul', Digit.mul_add3]
    apply (nat.zero_add (by{simp}:(ε::(0)).isZero)).trans
    simp[nat.eq]
    simp[mul] at ih
    exact (nat.zero_add (by{simp}:(ε::(0)).isZero)).symm.trans ih
  }
}
end Digits
end wkmath
