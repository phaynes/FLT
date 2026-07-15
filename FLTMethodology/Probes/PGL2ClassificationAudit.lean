/-
Copyright (c) 2026 Philip Haynes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philip Haynes
-/
module

import FLT.KnownIn1980s.PGL2.Defs

/-!
# Kernel audit for the public Dickson classification interface

This probe records the axiom closure of the public tame and wild classification declarations after
their proof development was moved below a cycle-free shared definitions module.
-/

#print axioms Dickson.classification_tame
#print axioms Dickson.classification_wild
