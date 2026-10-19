name = "arena/algebra"

///|
/// Runtime half of the system: no algebra, only frozen tables.
///
/// The `gen` rules re-run the compile-time engine of the sibling module
/// `../algebra-ct` on `spec/spec.txt` and write the result into the package
/// that consumes it.  They are declared at module level because they are used
/// from the packages' `dev_build`; they are the only build-time cost in the
/// whole system, because everything they produce is a constant.
rule(
  name: "gen-cub",
  command: "moon -C ../algebra-ct run cmd/gen --p 97 --n 1 --terms \"3.0:1|2.0:-6|1.0:11|0.0:-6\" --name cub > $output",
)

rule(
  name: "gen-fat",
  command: "moon -C ../algebra-ct run cmd/gen --p 7 --n 2 --terms \"2.0:1;1.1:1;0.2:1\" --name fatpoint > $output",
)

rule(
  name: "gen-wild",
  command: "moon -C ../algebra-ct run cmd/gen --p 2 --n 2 --terms \"2.0:1|0.0:-1;0.2:1|0.0:-1\" --name wild > $output",
)

rule(
  name: "gen-mix",
  command: "moon -C ../algebra-ct run cmd/gen --p 3 --n 2 --terms \"2.0:1|0.1:-1;0.3:1\" --name mix > $output",
)
