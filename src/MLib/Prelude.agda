module MLib.Prelude where

open import MLib.Prelude.FromStdlib public

module Fin where
  open import MLib.Prelude.Fin public
open Fin using (Fin) hiding (module Fin) public
