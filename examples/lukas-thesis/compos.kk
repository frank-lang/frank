// The 4 scenarios implemented in Koka

// Difference to the Frank counter-parts of some of the following functions:
// 1) Some are not effect-polymorphic here, whereas they are in Frank.
//    We believe this should be amenable though in principle, and that
//    we are just not Koka-savy enough yet to write it down (using the
//    forall quantifier + fun-construct somehow in combination /
//    anonymous fun's in Koka...)
// 2) They are not polymorphic in some type X but confined to int.
//    Since this is not our focus here, it does not matter (and could
//    probably easily be changed)

// Define effects
effect bchoice {
  fun bchoose() : bool
}

effect ichoice {
  fun ichoose() : int
}

// Basic handlers
val boolFix: forall <e,a> (() -> <bchoice|e>a) -> e a = handler {
  return x -> x
  bchoose()   -> resume(False)
}

val intFix: forall <e,a> (() -> <ichoice|e>a) -> e a = handler {
  return x -> x
  ichoose()   -> resume(42)
}

val boolByCons: forall <e,a> (() -> <console,bchoice|e>a) -> <console|e> a = handler {
  return x -> x
  bchoose()   -> resume(False) // we could use the console input here if we
                               // already knew the Koka library well enough...
}

// Scenario 1: Accumulating Effects
fun boolIntFix (act: () -> <ichoice,bchoice>int): int {
   boolFix({intFix(act)})
}

fun boolByConsIntFix (act: () -> <ichoice,bchoice,console>int): <console>int {
   boolByCons({intFix(act)})
}

// Scenario 2: Unintentionally Exposed Intermediate Effects
// The following signature does not type-check.
//   val intByBool: (() -> <ichoice>int) -> <bchoice>int
// However, this corresponds pretty much to the Frank setting
// (the adjustment is added to the ambient there, resulting in
// computation type with ability IChoice, BChoice as well).
val intByBool: forall<e> (() -> <ichoice,bchoice|e>int) -> <bchoice|e>int = handler {
    return x -> x
    ichoose() -> {if (bchoose())
                  then {if (bchoose()) then {resume(3)}
                                       else {resume(2)}}
                  else {if (bchoose()) then {resume(1)}
                                       else {resume(0)}}}
}

// This fixes it - but only because ichoose does take effect-carrying
// parameters (which cannot just be re-applied). It therefore is no
// real solution.
val intFix_composed: forall<e> (() -> <ichoice|e>int) -> e int = handler {
    return x -> x
    ichoose() -> { val a = boolFix({intByBool(ichoose)});
                   resume(a) }
}

// No problem here: bchoice does not get exposed.
val intByCons: forall<e> (() -> <ichoice,console|e>int) -> <console|e> int = handler {
    return x -> x
    ichoose() -> { val a = boolByCons({intByBool(ichoose)});
                   resume(a) }
}

// Scenario 3: Intentionally Exposed Intermediate Effects
// The following differs from the Frank counterpart: It is not
// polymorphic in its effects. We tried the subsequent toggled version
// or something similar, but to no success - however, we believe that
// this is only due to us not being Koka-savy enough.
fun boolIntFix_composed (act: () -> <bchoice,ichoice>int): int {
    boolFix({intByBool(act)})
}

// We believe in principle we can assign a definition to this signature
// val boolIntFix_composed_2: forall<e> (() -> <bchoice,ichoice|e>int) -> e int = handler {
//     return x -> x
//     bchoose() -> { resume(boolFix(bchoose)) }
//     ichoose() -> { resume(boolFix({intByBool(ichoose)})) }
// }

// Same here.
fun boolIntByCons (act: () -> <bchoice,ichoice>int): <console>int {
    boolByCons({intByBool(act)})
}

// Scenario 4: Intermediate Handling Without Introducing New Effects
val incrInt: (() -> <ichoice>int) -> <ichoice>int = handler {
    return x -> x
    ichoose() -> {val i = ichoose()
                  resume(i+1)}
}

// Works fine! (Just as in Frank now)
fun doubleIncrInt (act: () -> <ichoice>int): <ichoice>int {
  incrInt({incrInt(act)})
}


// For testing
fun booluser() : <bchoice> int {
  val b = bchoose()
  if (b) then { 3 }
         else { 7 }
}

fun intuser() : <ichoice> int {
  val i = ichoose()
  i
}

fun boolintuser() : <bchoice,ichoice> int {
  val b = bchoose()
  val i = ichoose()
  if (b) then { 1 + i }
         else { 100 + i }
}

fun main(): console ()
{
  intByCons({doubleIncrInt(ichoose)}).show.println
}
