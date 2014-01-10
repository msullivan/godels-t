module Eq where

open import Prelude
open import T
open import Contexts
open import Eq.Defs
import Eq.KleeneTheory
import Eq.ObsTheory
import Eq.LogicalTheory
import Eq.Theory

open Eq.Defs public
open Eq.KleeneTheory public using (kleene-is-equivalence ; nats-halt)
open Eq.ObsTheory public using (obs-is-coarsest ; obs-is-con-congruence)
open Eq.LogicalTheory public using (log-is-con-congruence)
open Eq.Theory public
