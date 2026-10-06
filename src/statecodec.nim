## Exact state encoding and compact per-variable interning, shared by explorers.

import std/tables
import nifcore, value, eval

type
  Interner* = object
    idx: Table[string, int32]
    encs: seq[string]

proc encodeState*(m: Module; st: State): string =
  for v in m.variables:
    encodeValue(st.vals[v], result)

proc decodeState*(m: Module; s: string): State =
  result = State(vals: initTable[SymId, Value]())
  var pos = 0
  for v in m.variables:
    result.vals[v] = decodeValue(m.vs, s, pos)

proc internState*(ins: var seq[Interner]; enc: string): string =
  ## Packed index tuple (4 bytes LE per variable), without fingerprinting.
  result = newStringOfCap(4 * ins.len)
  var pos = 0
  for i in 0 ..< ins.len:
    let start = pos
    skipEncodedValue(enc, pos)
    let seg = enc[start .. pos - 1]
    var id: int32
    ins[i].idx.withValue(seg, hit):
      id = hit[]
    do:
      id = int32(ins[i].encs.len)
      ins[i].encs.add seg
      ins[i].idx[seg] = id
    let u = uint32(id)
    result.add char(u and 0xff)
    result.add char((u shr 8) and 0xff)
    result.add char((u shr 16) and 0xff)
    result.add char((u shr 24) and 0xff)

proc unpackState*(ins: seq[Interner]; key: string): string =
  for i in 0 ..< ins.len:
    let p = 4 * i
    let id = uint32(key[p]) or (uint32(key[p+1]) shl 8) or
             (uint32(key[p+2]) shl 16) or (uint32(key[p+3]) shl 24)
    result.add ins[i].encs[int id]
