Util/Taktiks.vo Util/Taktiks.glob Util/Taktiks.v.beautified: Util/Taktiks.v
Util/Taktiks.vio: Util/Taktiks.v
Util/FSetNotin.vo Util/FSetNotin.glob Util/FSetNotin.v.beautified: Util/FSetNotin.v
Util/FSetNotin.vio: Util/FSetNotin.v
Util/ListFacts.vo Util/ListFacts.glob Util/ListFacts.v.beautified: Util/ListFacts.v
Util/ListFacts.vio: Util/ListFacts.v
Util/FiniteSets.vo Util/FiniteSets.glob Util/FiniteSets.v.beautified: Util/FiniteSets.v Util/ListFacts.vo
Util/FiniteSets.vio: Util/FiniteSets.v Util/ListFacts.vio
Util/FSetDecide.vo Util/FSetDecide.glob Util/FSetDecide.v.beautified: Util/FSetDecide.v
Util/FSetDecide.vio: Util/FSetDecide.v
Util/Atom.vo Util/Atom.glob Util/Atom.v.beautified: Util/Atom.v Util/FiniteSets.vo Util/FSetDecide.vo Util/FSetNotin.vo Util/ListFacts.vo
Util/Atom.vio: Util/Atom.v Util/FiniteSets.vio Util/FSetDecide.vio Util/FSetNotin.vio Util/ListFacts.vio
Util/Label.vo Util/Label.glob Util/Label.v.beautified: Util/Label.v Util/FiniteSets.vo Util/FSetDecide.vo Util/FSetNotin.vo Util/ListFacts.vo
Util/Label.vio: Util/Label.v Util/FiniteSets.vio Util/FSetDecide.vio Util/FSetNotin.vio Util/ListFacts.vio
Util/Nat.vo Util/Nat.glob Util/Nat.v.beautified: Util/Nat.v Util/Metatheory.vo
Util/Nat.vio: Util/Nat.v Util/Metatheory.vio
Util/AdditionalTactics.vo Util/AdditionalTactics.glob Util/AdditionalTactics.v.beautified: Util/AdditionalTactics.v
Util/AdditionalTactics.vio: Util/AdditionalTactics.v
Util/Environment.vo Util/Environment.glob Util/Environment.v.beautified: Util/Environment.v Util/ListFacts.vo Util/Atom.vo
Util/Environment.vio: Util/Environment.v Util/ListFacts.vio Util/Atom.vio
Util/Signatures.vo Util/Signatures.glob Util/Signatures.v.beautified: Util/Signatures.v Util/ListFacts.vo Util/Label.vo
Util/Signatures.vio: Util/Signatures.v Util/ListFacts.vio Util/Label.vio
Util/Metatheory.vo Util/Metatheory.glob Util/Metatheory.v.beautified: Util/Metatheory.v Util/AdditionalTactics.vo Util/Atom.vo Util/Environment.vo
Util/Metatheory.vio: Util/Metatheory.v Util/AdditionalTactics.vio Util/Atom.vio Util/Environment.vio
SystemC/CaptureSets.vo SystemC/CaptureSets.glob SystemC/CaptureSets.v.beautified: SystemC/CaptureSets.v Util/Metatheory.vo Util/Atom.vo Util/Label.vo Util/Nat.vo
SystemC/CaptureSets.vio: SystemC/CaptureSets.v Util/Metatheory.vio Util/Atom.vio Util/Label.vio Util/Nat.vio
SystemC/Definitions.vo SystemC/Definitions.glob SystemC/Definitions.v.beautified: SystemC/Definitions.v Util/Metatheory.vo SystemC/CaptureSets.vo Util/Signatures.vo
SystemC/Definitions.vio: SystemC/Definitions.v Util/Metatheory.vio SystemC/CaptureSets.vio Util/Signatures.vio
SystemC/Infrastructure.vo SystemC/Infrastructure.glob SystemC/Infrastructure.v.beautified: SystemC/Infrastructure.v Util/Taktiks.vo SystemC/Definitions.vo
SystemC/Infrastructure.vio: SystemC/Infrastructure.v Util/Taktiks.vio SystemC/Definitions.vio
SystemC/Lemmas.vo SystemC/Lemmas.glob SystemC/Lemmas.v.beautified: SystemC/Lemmas.v SystemC/Infrastructure.vo Util/Taktiks.vo Util/Signatures.vo
SystemC/Lemmas.vio: SystemC/Lemmas.v SystemC/Infrastructure.vio Util/Taktiks.vio Util/Signatures.vio
SystemC/Substitution.vo SystemC/Substitution.glob SystemC/Substitution.v.beautified: SystemC/Substitution.v Util/Taktiks.vo SystemC/Lemmas.vo
SystemC/Substitution.vio: SystemC/Substitution.v Util/Taktiks.vio SystemC/Lemmas.vio
SystemC/Soundness.vo SystemC/Soundness.glob SystemC/Soundness.v.beautified: SystemC/Soundness.v Util/Taktiks.vo SystemC/Substitution.vo Util/Signatures.vo
SystemC/Soundness.vio: SystemC/Soundness.v Util/Taktiks.vio SystemC/Substitution.vio Util/Signatures.vio
SystemC/Examples.vo SystemC/Examples.glob SystemC/Examples.v.beautified: SystemC/Examples.v SystemC/Definitions.vo SystemC/Lemmas.vo Util/Signatures.vo SystemC/Soundness.vo
SystemC/Examples.vio: SystemC/Examples.v SystemC/Definitions.vio SystemC/Lemmas.vio Util/Signatures.vio SystemC/Soundness.vio
