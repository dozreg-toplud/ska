import Lean

/-- The rewrite rules that run Nock: one per opcode, plus the rules for the
values that the opcodes produce. -/
register_simp_attr nock_exec
