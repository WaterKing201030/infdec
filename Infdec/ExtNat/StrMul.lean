import Infdec.ExtNat.Sub

namespace wkmath
namespace Digits
def strmul(x t:Digits):Digits:=
  if h:t.isZero then
    ε
  else
    have : t - One < t:=by{
      have h:One ≤ t:=(nat.one_le_iff_not_zero _).mpr h
      have h:t - One + One < t + One:=nat.lt_of_eq_of_lt (nat.sub_add_cancel h) (nat.lt_succ_self t)
      exact nat.add_left_lt_of_lt h
    }
    (strmul x (t - One)) ++ x
termination_by _ => t
end Digits
end wkmath
