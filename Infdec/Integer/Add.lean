import Infdec.Integer.Order

namespace wkmath
namespace int
def add:int → int → int
  | ⟨x0, true⟩, ⟨y0, true⟩ => ⟨x0 + y0, true⟩
  | ⟨x0, true⟩, ⟨y0, false⟩ => if y0 ≤ x0 then ⟨x0 - y0, true⟩ else ⟨y0 - x0, false⟩
  | ⟨x0, false⟩, ⟨y0, true⟩ => if y0 ≤ x0 then ⟨x0 - y0, false⟩ else ⟨y0 - x0, true⟩
  | ⟨x0, false⟩, ⟨y0, false⟩ => ⟨x0 + y0, false⟩

def add'(x y:int):int:=
  if x.negsign = y.negsign then
    ⟨x.digits + y.digits, x.negsign⟩
  else
    (if y.digits ≤ x.digits then ⟨x.digits - y.digits, x.negsign⟩ else ⟨y.digits - x.digits, y.negsign⟩)

theorem add_eq_add'{x y:int}:add x y = add' x y:=
  match x, y with
  | ⟨_, true⟩, ⟨_, true⟩
  | ⟨_, false⟩, ⟨_, false⟩
  | ⟨_, true⟩, ⟨_, false⟩
  | ⟨_, false⟩, ⟨_, true⟩ => rfl

infixl:65 " + " => add

def sub(x y:int):int:=
  x + (- y)

infixl:65 " - " => sub

theorem add.comm(x y:int):x + y =I y + x:=by{
  match x, y with
  | ⟨x0, true⟩, ⟨y0, true⟩
  | ⟨x0, false⟩, ⟨y0, false⟩ => {
    simp[add]
    rw[Digits.add.comm]
    exact eq.refl ⟨y0 + x0, _⟩
  }
  | ⟨x0, true⟩, ⟨y0, false⟩
  | ⟨x0, false⟩, ⟨y0, true⟩ => {
    simp[add]
    cases Digits.nat.le_or_gt x0 y0 with
    | inl h => {
      rw[Digits.nat.le_iff_eq_or_lt] at h
      cases h with
      | inl h => {
        simp[h.to_le, h.symm.to_le]
        have h0:=Digits.nat.nat_eq_sub_zero h
        have h1:=Digits.nat.nat_eq_sub_zero h.symm
        rw[eq]
        simp[h0, h1]
      }
      | inr h => {
        have h':=Digits.nat.lt_iff_not_ge.mp h
        simp[h', h.to_le]
        exact eq.refl ⟨y0 - x0, _⟩
      }
    }
    | inr h => {
      simp[h.to_le, Digits.nat.lt_iff_not_ge.mp h]
      exact eq.refl ⟨x0 - y0, _⟩
    }
  }
}

theorem add.assoc(x y z:int):x + y + z =I x + (y + z):=by{
  match x, y, z with
  | ⟨x0, true⟩, ⟨y0, true⟩, ⟨z0, true⟩
  | ⟨x0, false⟩, ⟨y0, false⟩, ⟨z0, false⟩ => {
    simp[add]
    rw[Digits.add.assoc]
    exact eq.refl ⟨x0 + (y0 + z0), _⟩
  }
  | ⟨x0, false⟩, ⟨y0, true⟩, ⟨z0, true⟩
  | ⟨x0, true⟩, ⟨y0, false⟩, ⟨z0, false⟩ => {
    cases Decidable.em (y0 ≤ x0) with
    | inl h => {
      simp[add, h]
      cases Digits.nat.le_or_gt (y0 + z0) x0 with
      | inl h' => {
        simp[h']
        have h'':z0 ≤ x0 - y0:=by{
          rw[Digits.add.comm] at h'
          have h'': x0 =N x0 - y0 + y0 := (Digits.nat.sub_add_cancel h).symm
          have h':=Digits.nat.le_of_le_of_eq h' h''
          exact Digits.nat.add_left_le_of_le h'
        }
        simp[h'']
        exact same_sign_nat_eq_to_eq_intro (Digits.nat.sub_add_eq_sub_sub x0 y0 z0).symm (Eq.refl _)
      }
      | inr h' => {
        have h'':x0 - y0 < z0:=by{
          rw[Digits.add.comm] at h'
          have h':=Digits.nat.lt_of_eq_of_lt (Digits.nat.sub_add_cancel h) h'
          exact Digits.nat.add_left_lt_of_lt h'
        }
        simp[Digits.nat.lt_iff_not_ge.mp h', Digits.nat.lt_iff_not_ge.mp h'']
        apply λ h => same_sign_nat_eq_to_eq_intro h (Eq.refl _)
        rw[Digits.add.comm] at h'
        apply (Digits.nat.sub_sub_eq_sub_add h'.to_le h).trans
        rw[Digits.add.comm]
        exact Digits.nat.eq.refl _
      }
    }
    | inr h => {
      simp[add, h]
      cases Decidable.em (y0 + z0 ≤ x0) with
      | inl h' => {
        exact (h ((Digits.nat.add_right_le y0 z0).trans h')).elim
      }
      | inr h' => {
        simp[h']
        apply λ h => same_sign_nat_eq_to_eq_intro h (Eq.refl _)
        rw[←Digits.nat.lt_iff_not_ge] at h
        exact Digits.nat.add_sub_comm h.to_le z0
      }
    }
  }
  | ⟨x0, true⟩, ⟨y0, true⟩, ⟨z0, false⟩
  | ⟨x0, false⟩, ⟨y0, false⟩, ⟨z0, true⟩ => {
    cases Decidable.em (z0 ≤ y0) with
    | inl h => {
      have h':=h.trans (Digits.nat.add_left_le x0 y0)
      simp[add, h, h']
      apply λ h => same_sign_nat_eq_to_eq_intro h (Eq.refl _)
      exact Digits.nat.add_sub_assoc x0 h
    }
    | inr h => {
      cases Decidable.em (z0 ≤ x0 + y0) with
      | inl h' => {
        simp[add, h, h']
        have h'':z0 - y0 ≤ x0:=by{
          have h:=Digits.nat.lt_of_not_ge h
          have h:z0 - y0 + y0 ≤ x0 + y0:=Digits.nat.le_of_eq_of_le (Digits.nat.sub_add_cancel h.to_le) h'
          exact Digits.nat.add_left_le_of_le h
        }
        simp[h'']
        apply λ h => same_sign_nat_eq_to_eq_intro h (Eq.refl _)
        rw[←Digits.nat.lt_iff_not_ge] at h
        exact (Digits.nat.sub_sub_eq_sub_add h' h.to_le).symm
      }
      | inr h' => {
        simp[add, h, h']
        have h'':¬z0 - y0 ≤ x0:=by{
          rw[←Digits.nat.lt_iff_not_ge] at *
          exact Digits.nat.add_left_lt_of_lt (Digits.nat.lt_of_lt_of_eq h' (Digits.nat.sub_add_cancel h.to_le).symm)
        }
        simp[h'']
        apply λ h => same_sign_nat_eq_to_eq_intro h (Eq.refl _)
        exact (Digits.nat.sub_add_eq_sub_sub z0 x0 y0).trans (Digits.nat.sub_comm z0 x0 y0)
      }
    }
  }
  | ⟨x0, true⟩, ⟨y0, false⟩, ⟨z0, true⟩
  | ⟨x0, false⟩, ⟨y0, true⟩, ⟨z0, false⟩ => {
    cases Decidable.em (y0 ≤ x0) with
    | inl h => {
      cases Decidable.em (z0 ≤ y0) with
      | inl h' => {
        simp[add, h, h']
        have h'':y0 - z0 ≤ x0:=(Digits.nat.sub_le y0 z0).trans h
        simp[h'']
        apply λ h => same_sign_nat_eq_to_eq_intro h (Eq.refl _)
        have h'':y0 ≤ x0 + z0:=h.trans (Digits.nat.add_right_le x0 z0)
        exact (Digits.nat.add_sub_comm h z0).trans (Digits.nat.sub_sub_eq_sub_add h'' h').symm
      }
      | inr h' => {
        simp[add, h, h']
        apply λ h => same_sign_nat_eq_to_eq_intro h (Eq.refl _)
        have h':=Digits.nat.lt_of_not_ge h'
        exact (Digits.nat.add_sub_comm h z0).trans (Digits.nat.add_sub_assoc x0 h'.to_le)
      }
    }
    | inr h => {
      cases Decidable.em (z0 ≤ y0) with
      | inl h' => {
        simp[add, h, h']
        rw[←Digits.nat.lt_iff_not_ge] at h
        cases Decidable.em (x0 + z0 ≤ y0) with
        | inl h'' => {
          have h''':z0 ≤ y0 - x0:=by{
            rw[Digits.add.comm] at h''
            exact Digits.nat.add_left_le_of_le (Digits.nat.le_of_le_of_eq h'' (Digits.nat.sub_add_cancel h.to_le).symm)
          }
          simp[h''']
          rw[Digits.nat.le_iff_eq_or_lt] at h''
          cases h'' with
          | inl h'' => {
            have h''':y0 - z0 ≤ x0:=Digits.nat.add_left_le_of_le ((Digits.nat.sub_add_cancel h').trans h''.symm).to_le
            simp[h''']
            have h0:(y0 - (x0 + z0)).isZero:=Digits.nat.nat_eq_sub_zero h''.symm
            have h1:(x0 + z0 - y0).isZero:=Digits.nat.nat_eq_sub_zero h''
            apply zero_to_eq_intro
            exact Digits.nat_eq_zero_isZero (Digits.nat.sub_add_eq_sub_sub _ _ _) h0
            exact Digits.nat_eq_zero_isZero' (Digits.nat.sub_sub_eq_sub_add h''.symm.to_le h') h1
          }
          | inr h'' => {
            have h''':¬y0 - z0 ≤ x0:=by{
              rw[←Digits.nat.lt_iff_not_ge]
              exact Digits.nat.add_left_lt_of_lt (Digits.nat.lt_of_lt_of_eq h'' (Digits.nat.sub_add_cancel h').symm)
            }
            simp[h''']
            apply λ h => same_sign_nat_eq_to_eq_intro h (Eq.refl _)
            exact Digits.nat.sub_comm _ _ _
          }
        }
        | inr h'' => {
          rw[←Digits.nat.lt_iff_not_ge] at h''
          have h''':¬z0 ≤ y0 - x0:=by{
            rw[←Digits.nat.lt_iff_not_ge]
            rw[Digits.add.comm] at h''
            exact Digits.nat.add_left_lt_of_lt (Digits.nat.lt_of_eq_of_lt (Digits.nat.sub_add_cancel h.to_le) h'')
          }
          simp[h''']
          have h''':y0 - z0 ≤ x0:=(Digits.nat.add_left_lt_of_lt (Digits.nat.lt_of_eq_of_lt (Digits.nat.sub_add_cancel h') h'')).to_le
          simp[h''']
          apply λ h => same_sign_nat_eq_to_eq_intro h (Eq.refl _)
          have h''':y0 < z0 + x0:=by{
            rw[Digits.add.comm]
            exact h''
          }
          apply (Digits.nat.sub_sub_eq_sub_add h'''.to_le h.to_le).trans
          apply λ h => Digits.nat.eq.trans h (Digits.nat.sub_sub_eq_sub_add h''.to_le h').symm
          rw[Digits.add.comm]
          exact Digits.nat.eq.refl _
        }
      }
      | inr h' => {
        simp[add, h, h']
        rw[←Digits.nat.lt_iff_not_ge] at *
        have h'':¬z0 ≤ y0 - x0:=by{
          rw[←Digits.nat.lt_iff_not_ge]
          exact Digits.nat.lt_of_le_of_lt (Digits.nat.sub_le y0 x0) h'
        }
        simp[h'']
        apply λ h => same_sign_nat_eq_to_eq_intro h (Eq.refl _)
        rw[←Digits.nat.lt_iff_not_ge] at h''
        have h''':y0 ≤ z0 + x0 := (Digits.nat.lt_of_eq_of_lt (Digits.nat.sub_add_cancel h.to_le).symm (Digits.nat.lt_of_add_left_lt h'' x0)).to_le
        apply (Digits.nat.sub_sub_eq_sub_add h''' h.to_le).trans
        rw[Digits.add.comm]
        exact Digits.nat.add_sub_assoc x0 h'.to_le
      }
    }
  }
}

theorem add_neg_eq_zero(x:int):(x + -x).isZero:=by{
  match x with
  | ⟨x0, true⟩
  | ⟨x0, false⟩ => {
    simp[add, neg, Digits.nat.le.refl x0]
    rw[isZero]
    exact Digits.nat.nat_eq_sub_zero (Digits.nat.eq.refl _)
  }
}

theorem add_zero(x:int){y:int}(h:y.isZero):x + y =I x:=by{
  rw[isZero] at h
  match x, y with
  | ⟨x0, x1⟩, ⟨y0, y1⟩ => {
    match x1, y1 with
    | true, true
    | false, false => simp[add];exact same_sign_nat_eq_to_eq_intro (Digits.nat.add_zero h) (Eq.refl _)
    | true, false
    | false, true => {
      have h':y0.isZero:=h
      have h':=Digits.nat.zero_le x0 h'
      simp[add, h']
      exact same_sign_nat_eq_to_eq_intro (Digits.nat.sub_zero_nat_eq x0 h) (Eq.refl _)
    }
  }
}

theorem zero_add{x:int}(h:x.isZero)(y:int):x + y =I y:=
  (add.comm _ _).trans (add_zero _ h)

theorem add_congr{x y z w:int}(h0:x =I z)(h1:y =I w):x + y =I z + w:=by{
  match x, y, z, w with
  | ⟨x0, x1⟩, ⟨y0, y1⟩, ⟨z0, z1⟩, ⟨w0, w1⟩ => {
    cases Decidable.em (y0.isZero) with
    | inl h2 => {
      simp[eq] at h1
      simp[h2] at h1
      have h2:(⟨y0, y1⟩:int).isZero:=h2
      have h1:(⟨w0, w1⟩:int).isZero:=h1
      exact (add_zero _ h2).trans (h0.trans (add_zero _ h1).symm)
    }
    | inr h2 => {
      simp[eq] at h0
      cases Decidable.em (x0.isZero) with
      | inl h3 => {
        simp[h3] at h0
        have h0:(⟨z0, z1⟩:int).isZero:=h0
        have h3:(⟨x0, x1⟩:int).isZero:=h3
        apply (add.comm _ _).trans
        apply eq.symm
        apply (add.comm _ _).trans
        apply (add_zero _ h0).trans
        apply eq.symm
        apply (add_zero _ h3).trans
        exact h1
      }
      | inr h3 => {
        simp[h3] at h0
        simp[eq] at h1
        simp[h2] at h1
        simp[h0.right, h1.right]
        match z1, w1 with
        | true, true
        | false, false => {
          simp[add]
          apply same_sign_nat_eq_to_eq
          simp
          exact Digits.nat.eq_of_eq_add_eq h0.left h1.left
          simp
        }
        | true, false
        | false, true => {
          simp[add]
          cases Decidable.em (y0 ≤ x0) with
          | inl h => {
            have h':w0 ≤ z0:=Digits.nat.le_of_le_of_eq (Digits.nat.le_of_eq_of_le h1.left.symm h) h0.left
            simp[h, h']
            apply same_sign_nat_eq_to_eq
            simp
            exact Digits.nat.eq_of_eq_sub_eq h0.left h1.left
            simp
          }
          | inr h => {
            have h':¬w0 ≤ z0:=λ h' => h (Digits.nat.le_of_le_of_eq (Digits.nat.le_of_eq_of_le h1.left h') h0.left.symm)
            simp[h, h']
            apply same_sign_nat_eq_to_eq
            simp
            exact Digits.nat.eq_of_eq_sub_eq h1.left h0.left
            simp
          }
        }
      }
    }
  }
}

theorem sub_congr{x y z w:int}(h0:x =I y)(h1:z =I w):x - z =I y - w:=by{
  simp[sub]
  have h1:=neg_eq_of_eq h1
  exact add_congr h0 h1
}

theorem sub_add_comm(x y z:int):x - y + z =I x + z - y:=by{
  simp[sub]
  exact ((add.assoc _ _ _).trans (add_congr (eq.refl x) (add.comm y.neg z))).trans (add.assoc _ _ _).symm
}

theorem add_sub_cancel(x y:int):x + y - y =I x:=
  (add.assoc _ _ _).trans (add_zero x (add_neg_eq_zero y))

theorem sub_add_cancel(x y:int):x - y + y =I x:=
  (sub_add_comm _ _ _).trans (add_sub_cancel _ _)

theorem add_toStdInt_eq_toStdInt_add(x y:int):(x + y).toStdInt =I (x.toStdInt) + y.toStdInt:=
  (toStdInt_eq (x + y)).trans (add_congr (toStdInt_eq x).symm (toStdInt_eq y).symm)

theorem sub_toStdInt_eq_toStdInt_sub(x y:int):(x - y).toStdInt =I x.toStdInt - y.toStdInt:=
  (add_toStdInt_eq_toStdInt_add x (-y)).trans (add_congr (eq.refl _) (neg_toStdInt_eq_toStdInt_neg y))
end int
end wkmath
