# Chang's fork of Ascent

This is a fork of Ascent plus plus by Yihao, forked from a rust based datalog dailect made by [Arash](https://github.com/s-arash)

# What's new in this fork?

* New stuff from [Yihao](https://github.com/StarGazerM)
* Added the capture! macro to record the rule-matching state as plain text and pass it as a callback argument
* Implemented yaml based provenance tracking to make debugging easier
* Added automatic **semiring provenance** threading: tag a relation with `#[semiring(K)]` and the engine annotates every derived tuple with a value in a commutative semiring (shortest paths, confidence, why-provenance, …). See [SEMIRING.MD](SEMIRING.MD).