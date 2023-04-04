import Proost.Elab.Raw
import Proost.Kernel.Level

def RawLevel.toCore : RawLevel → Level
  | num n => OfNat.ofNat n
  | _ => sorry