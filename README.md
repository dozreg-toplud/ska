# Subject Knowledge Analysis (SKA)

This repo contains an Urbit desk to:
  1. Run analysis on Nock subject-formula which produces a static call graph;
  2. Compile functions from that call graph to an intermediate representation form that deconstructs the subject into a flat list of arguments, reducing core-editing overhead that comes from Hoon calling convention;
  3. Run optimizations on that IR, simplifying the output code;
  4. Providing a stateful Arvo-shaped core definition for Vere integration.

Initially based on [@zorp-corp/sword](https://github.com/zorp-corp/sword), this project underwent significant changes in the implementation of the originally envisioned algorithm.

## Reading/watching recommendations

[`nock-compilation.hoon`](https://github.com/dozreg-toplud/ska/blob/master/desk/lib/nock-compilation.hoon) is the single-file implementation of the algortihm. The rest of the repo contains some historical artifacts and tests. The file is heavily commented so it should be a good read on its own.

### Papers/presentations about the latest implementation

  - [Nock Compilation (Subject Knowledge Analysis II)](https://urbitsystems.tech/issue/v03-i02)

### Historical articles/videos:
  - [First presentation of SKA by Edward Amsden @ Lambdaconf](https://www.youtube.com/watch?v=8vtnmiEN-r4) 
  - [Second presentation by Edward Amsden and Joe Bryan @ Lake Summit](https://www.youtube.com/watch?v=z24zWdHfVfI)
  - [My USTJ article on the first reimplementation of SKA](https://urbitsystems.tech/article/v03-i01/subject-knowledge-analysis)
