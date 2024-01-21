import Infdec.Nat.NatAddOrder

namespace wkmath
namespace Digits
def mul':Digits → Digit → Digit → Digits
  | ε, _, c => match c with
    | (0) => ε
    | (1) => ε::(1)
    | (2) => ε::(2)
  | xs::xd, d, c => (mul' xs d (Digit.mul_add3 xd d c).fst)::(Digit.mul_add3 xd d c).snd

def mul:Digits → Digits → Digits
  | _, ε => ε
  | x, ys::yd => (x.mul ys)::(0) + (x.mul' yd (0))
end Digits
end wkmath
