import { hash } from './Hash';
import { is } from './is';

import {
  utilArrCopy,
  utilArrSetAt,
  utilArrSpliceIn,
  utilArrSpliceOut,
} from './util';

import { SHIFT, SIZE, MASK, NOT_SET, OwnerID, SetRef } from './TrieUtils';

const MAX_ARRAY_MAP_SIZE = SIZE / 4;
const MAX_BITMAP_INDEXED_SIZE = SIZE / 2;
const MIN_HASH_ARRAY_MAP_SIZE = SIZE / 4;

const nodeHashArrayMapGet = (nham, shift, keyHash, key, notSetValue) => {
  if (keyHash === undefined) {
    keyHash = hash(key);
  }
  const idx = (shift === 0 ? keyHash : keyHash >>> shift) & MASK;
  const node = nham.nodes[idx];
  return node
    ? node.get(shift + SHIFT, keyHash, key, notSetValue)
    : notSetValue;
};

const nodeHashArrayMapUpdate = (
  nham,
  ownerID,
  shift,
  keyHash,
  key,
  value,
  didChangeSize,
  didAlter
) => {
  if (keyHash === undefined) {
    keyHash = hash(key);
  }
  const idx = (shift === 0 ? keyHash : keyHash >>> shift) & MASK;
  const removed = value === NOT_SET;
  const nodes = nham.nodes;
  const node = nodes[idx];

  if (removed && !node) {
    return nham;
  }

  const newNode = nodeUpdate(
    node,
    ownerID,
    shift + SHIFT,
    keyHash,
    key,
    value,
    didChangeSize,
    didAlter
  );
  if (newNode === node) {
    return nham;
  }

  let newCount = nham.count;
  if (!node) {
    newCount++;
  } else if (!newNode) {
    newCount--;
    if (newCount < MIN_HASH_ARRAY_MAP_SIZE) {
      return nodesPack(ownerID, nodes, newCount, idx);
    }
  }

  const isEditable = ownerID && ownerID === nham.ownerID;
  const newNodes = utilArrSetAt(nodes, idx, newNode, isEditable);

  if (isEditable) {
    nham.count = newCount;
    nham.nodes = newNodes;
    return nham;
  }

  return new NodeHashArrayMap(ownerID, newCount, newNodes);
};

const nodeHashArrayMapCreate = (ownerID, count, nodes, nham = {}) => {
  nham.ownerID = ownerID;
  nham.count = count;
  nham.nodes = nodes;

  return nham;
};

class NodeHashArrayMap {
  constructor(ownerID, count, nodes) {
    nodeHashArrayMapCreate(ownerID, count, nodes, this);
  }

  get(shift, keyHash, key, notSetValue) {
    return nodeHashArrayMapGet(this, shift, keyHash, key, notSetValue);
  }

  update(ownerID, shift, keyHash, key, value, didChangeSize, didAlter) {
    return nodeHashArrayMapUpdate(
      this,
      ownerID,
      shift,
      keyHash,
      key,
      value,
      didChangeSize,
      didAlter
    );
  }
}

const nodeHashCollisionCreate = (ownerID, keyHash, entries, nhc) => {
  nhc.ownerID = ownerID;
  nhc.keyHash = keyHash;
  nhc.entries = entries;

  return nhc;
};

const nodeHashCollisionUpdate = (
  nhc,
  ownerID,
  shift,
  keyHash,
  key,
  value,
  didChangeSize,
  didAlter
) => {
  if (keyHash === undefined) {
    keyHash = hash(key);
  }

  const removed = value === NOT_SET;

  if (keyHash !== nhc.keyHash) {
    if (removed) {
      return nhc;
    }
    SetRef(didAlter);
    SetRef(didChangeSize);
    return nodeMergeInto(nhc, ownerID, shift, keyHash, [key, value]);
  }

  const entries = nhc.entries;
  let idx = 0;
  const len = entries.length;
  for (; idx < len; idx++) {
    if (is(key, entries[idx][0])) {
      break;
    }
  }
  const exists = idx < len;

  if (exists ? entries[idx][1] === value : removed) {
    return nhc;
  }

  SetRef(didAlter);
  // eslint-disable-next-line @typescript-eslint/no-unused-expressions -- TODO enable eslint here
  (removed || !exists) && SetRef(didChangeSize);

  if (removed && len === 2) {
    return new NodeValue(ownerID, nhc.keyHash, entries[idx ^ 1]);
  }

  const isEditable = ownerID && ownerID === nhc.ownerID;
  const newEntries = isEditable ? entries : utilArrCopy(entries);

  if (exists) {
    if (removed) {
      // eslint-disable-next-line @typescript-eslint/no-unused-expressions -- TODO enable eslint here
      idx === len - 1 ? newEntries.pop() : (newEntries[idx] = newEntries.pop());
    } else {
      newEntries[idx] = [key, value];
    }
  } else {
    newEntries.push([key, value]);
  }

  if (isEditable) {
    nhc.entries = newEntries;
    return nhc;
  }

  return new NodeHashCollision(ownerID, nhc.keyHash, newEntries);
};

// was HashCollisionNode
class NodeHashCollision {
  constructor(ownerID, keyHash, entries) {
    nodeHashCollisionCreate(ownerID, keyHash, entries, this);
  }

  get(shift, keyHash, key, notSetValue) {
    return nodeEntryGet(this, shift, keyHash, key, notSetValue);
  }

  update(ownerID, shift, keyHash, key, value, didChangeSize, didAlter) {
    return nodeHashCollisionUpdate(
      this,
      ownerID,
      shift,
      keyHash,
      key,
      value,
      didChangeSize,
      didAlter
    );
  }
}

const nodesExpand = (ownerID, nodes, bitmap, including, node) => {
  let count = 0;
  const expandedNodes = new Array(SIZE);
  for (let ii = 0; bitmap !== 0; ii++, bitmap >>>= 1) {
    expandedNodes[ii] = bitmap & 1 ? nodes[count++] : undefined;
  }
  expandedNodes[including] = node;
  return new NodeHashArrayMap(ownerID, count + 1, expandedNodes);
};

const nodeMergeInto = (node, ownerID, shift, keyHash, entry) => {
  if (node.keyHash === keyHash) {
    return new NodeHashCollision(ownerID, keyHash, [node.entry, entry]);
  }

  const idx1 = (shift === 0 ? node.keyHash : node.keyHash >>> shift) & MASK;
  const idx2 = (shift === 0 ? keyHash : keyHash >>> shift) & MASK;

  let newNode;
  const nodes =
    idx1 === idx2
      ? [nodeMergeInto(node, ownerID, shift + SHIFT, keyHash, entry)]
      : ((newNode = new NodeValue(ownerID, keyHash, entry)),
        idx1 < idx2 ? [node, newNode] : [newNode, node]);

  return new NodeBitmapIndexed(ownerID, (1 << idx1) | (1 << idx2), nodes);
};

const nodeValueCreate = (ownerID, keyHash, entry, nv) => {
  nv.ownerID = ownerID;
  nv.keyHash = keyHash;
  nv.entry = entry;

  return nv;
};

const nodeValueGet = (nv, shift, keyHash, key, notSetValue) => {
  return is(key, nv.entry[0]) ? nv.entry[1] : notSetValue;
};

const nodeValueUpdate = (
  nv,
  ownerID,
  shift,
  keyHash,
  key,
  value,
  didChangeSize,
  didAlter
) => {
  const removed = value === NOT_SET;
  const keyMatch = is(key, nv.entry[0]);
  if (keyMatch ? value === nv.entry[1] : removed) {
    return nv;
  }

  SetRef(didAlter);

  if (removed) {
    SetRef(didChangeSize);
    return; // undefined
  }

  if (keyMatch) {
    if (ownerID && ownerID === nv.ownerID) {
      nv.entry[1] = value;
      return nv;
    }
    return new NodeValue(ownerID, nv.keyHash, [key, value]);
  }

  SetRef(didChangeSize);
  return nodeMergeInto(nv, ownerID, shift, hash(key), [key, value]);
};

class NodeValue {
  constructor(ownerID, keyHash, entry) {
    nodeValueCreate(ownerID, keyHash, entry, this);
  }

  get(shift, keyHash, key, notSetValue) {
    return nodeValueGet(this, shift, keyHash, key, notSetValue);
  }

  update(ownerID, shift, keyHash, key, value, didChangeSize, didAlter) {
    return nodeValueUpdate(
      this,
      ownerID,
      shift,
      keyHash,
      key,
      value,
      didChangeSize,
      didAlter
    );
  }
}

const nodeIsLeaf = (node) => {
  return (
    node.constructor === NodeValue || node.constructor === NodeHashCollision
  );
};

const nodesPack = (ownerID, nodes, count, excluding) => {
  let bitmap = 0;
  let packedII = 0;
  const packedNodes = new Array(count);
  for (let ii = 0, bit = 1, len = nodes.length; ii < len; ii++, bit <<= 1) {
    const node = nodes[ii];
    if (node !== undefined && ii !== excluding) {
      bitmap |= bit;
      packedNodes[packedII++] = node;
    }
  }
  return new NodeBitmapIndexed(ownerID, bitmap, packedNodes);
};

const nodeUpdate = (
  node,
  ownerID,
  shift,
  keyHash,
  key,
  value,
  didChangeSize,
  didAlter
) => {
  if (!node) {
    if (value === NOT_SET) {
      return node;
    }
    SetRef(didAlter);
    SetRef(didChangeSize);
    return new NodeValue(ownerID, keyHash, [key, value]);
  }
  return node.update(
    ownerID,
    shift,
    keyHash,
    key,
    value,
    didChangeSize,
    didAlter
  );
};

const popCount = (x) => {
  x -= (x >> 1) & 0x55555555;
  x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
  x = (x + (x >> 4)) & 0x0f0f0f0f;
  x += x >> 8;
  x += x >> 16;
  return x & 0x7f;
};

const nodeBitmapIndexedCreate = (ownerID, bitmap, nodes, nbi) => {
  nbi.ownerID = ownerID;
  nbi.bitmap = bitmap;
  nbi.nodes = nodes;

  return nbi;
};

const nodeBitmapIndexedGet = (nbi, shift, keyHash, key, notSetValue) => {
  if (keyHash === undefined) {
    keyHash = hash(key);
  }
  const bit = 1 << ((shift === 0 ? keyHash : keyHash >>> shift) & MASK);
  const bitmap = nbi.bitmap;
  return (bitmap & bit) === 0
    ? notSetValue
    : nbi.nodes[popCount(bitmap & (bit - 1))].get(
        shift + SHIFT,
        keyHash,
        key,
        notSetValue
      );
};

const nodeBitmapIndexedUpdate = (
  nbi,
  ownerID,
  shift,
  keyHash,
  key,
  value,
  didChangeSize,
  didAlter
) => {
  if (keyHash === undefined) {
    keyHash = hash(key);
  }
  const keyHashFrag = (shift === 0 ? keyHash : keyHash >>> shift) & MASK;
  const bit = 1 << keyHashFrag;
  const bitmap = nbi.bitmap;
  const exists = (bitmap & bit) !== 0;

  if (!exists && value === NOT_SET) {
    return nbi;
  }

  const idx = popCount(bitmap & (bit - 1));
  const nodes = nbi.nodes;
  const node = exists ? nodes[idx] : undefined;
  const newNode = nodeUpdate(
    node,
    ownerID,
    shift + SHIFT,
    keyHash,
    key,
    value,
    didChangeSize,
    didAlter
  );

  if (newNode === node) {
    return nbi;
  }

  if (!exists && newNode && nodes.length >= MAX_BITMAP_INDEXED_SIZE) {
    return nodesExpand(ownerID, nodes, bitmap, keyHashFrag, newNode);
  }

  if (exists && !newNode && nodes.length === 2 && nodeIsLeaf(nodes[idx ^ 1])) {
    return nodes[idx ^ 1];
  }

  if (exists && newNode && nodes.length === 1 && nodeIsLeaf(newNode)) {
    return newNode;
  }

  const isEditable = ownerID && ownerID === nbi.ownerID;
  const newBitmap = exists ? (newNode ? bitmap : bitmap ^ bit) : bitmap | bit;
  const newNodes = exists
    ? newNode
      ? utilArrSetAt(nodes, idx, newNode, isEditable)
      : utilArrSpliceOut(nodes, idx, isEditable)
    : utilArrSpliceIn(nodes, idx, newNode, isEditable);

  if (isEditable) {
    nbi.bitmap = newBitmap;
    nbi.nodes = newNodes;
    return nbi;
  }

  return new NodeBitmapIndexed(ownerID, newBitmap, newNodes);
};

class NodeBitmapIndexed {
  constructor(ownerID, bitmap, nodes) {
    nodeBitmapIndexedCreate(ownerID, bitmap, nodes, this);
  }

  get(shift, keyHash, key, notSetValue) {
    return nodeBitmapIndexedGet(this, shift, keyHash, key, notSetValue);
  }

  update(ownerID, shift, keyHash, key, value, didChangeSize, didAlter) {
    return nodeBitmapIndexedUpdate(
      this,
      ownerID,
      shift,
      keyHash,
      key,
      value,
      didChangeSize,
      didAlter
    );
  }
}

const nodeEntryGet = (nam, shift, keyHash, key, notSetValue) => {
  const entries = nam.entries;
  for (let ii = 0, len = entries.length; ii < len; ii++) {
    if (is(key, entries[ii][0])) {
      return entries[ii][1];
    }
  }
  return notSetValue;
};

const nodeArrayMapUpdate = (
  nam,
  ownerID,
  shift,
  keyHash,
  key,
  value,
  didChangeSize,
  didAlter
) => {
  const removed = value === NOT_SET;

  const entries = nam.entries;
  let idx = 0;
  const len = entries.length;
  for (; idx < len; idx++) {
    if (is(key, entries[idx][0])) {
      break;
    }
  }
  const exists = idx < len;

  if (exists ? entries[idx][1] === value : removed) {
    return nam;
  }

  SetRef(didAlter);
  // eslint-disable-next-line @typescript-eslint/no-unused-expressions -- TODO enable eslint here
  (removed || !exists) && SetRef(didChangeSize);

  if (removed && entries.length === 1) {
    return; // undefined
  }

  if (!exists && !removed && entries.length >= MAX_ARRAY_MAP_SIZE) {
    return nodesCreate(ownerID, entries, key, value);
  }

  const isEditable = ownerID && ownerID === nam.ownerID;
  const newEntries = isEditable ? entries : utilArrCopy(entries);

  if (exists) {
    if (removed) {
      // eslint-disable-next-line @typescript-eslint/no-unused-expressions -- TODO enable eslint here
      idx === len - 1 ? newEntries.pop() : (newEntries[idx] = newEntries.pop());
    } else {
      newEntries[idx] = [key, value];
    }
  } else {
    newEntries.push([key, value]);
  }

  if (isEditable) {
    nam.entries = newEntries;
    return nam;
  }

  return new NodeArrayMap(ownerID, newEntries);
};

const nodeArrayMapCreate = (ownerID, entries, nam) => {
  nam.ownerID = ownerID;
  nam.entries = entries;

  return nam;
};

class NodeArrayMap {
  constructor(ownerID, entries) {
    nodeArrayMapCreate(ownerID, entries, this);
  }

  get(shift, keyHash, key, notSetValue) {
    return nodeEntryGet(this, shift, keyHash, key, notSetValue);
  }

  update(ownerID, shift, keyHash, key, value, didChangeSize, didAlter) {
    return nodeArrayMapUpdate(
      this,
      ownerID,
      shift,
      keyHash,
      key,
      value,
      didChangeSize,
      didAlter
    );
  }
}

const nodesCreate = (ownerID, entries, key, value) => {
  if (!ownerID) {
    ownerID = new OwnerID();
  }
  let node = new NodeValue(ownerID, hash(key), [key, value]);
  for (let ii = 0; ii < entries.length; ii++) {
    const entry = entries[ii];
    node = node.update(ownerID, 0, undefined, entry[0], entry[1]);
  }
  return node;
};

export {
  NodeArrayMap,
  NodeHashArrayMap,
  NodeHashCollision,
  NodeBitmapIndexed,
  NodeValue,
  nodeArrayMapCreate,
  nodeArrayMapUpdate,
  nodeHashArrayMapCreate,
  nodeHashArrayMapGet,
  nodeHashArrayMapUpdate,
  nodeHashCollisionCreate,
  nodeHashCollisionUpdate,
  nodeBitmapIndexedCreate,
  nodeBitmapIndexedGet,
  nodeBitmapIndexedUpdate,
  nodesExpand,
  nodesPack,
  nodesCreate,
  nodeEntryGet,
  nodeMergeInto,
  nodeIsLeaf,
  nodeUpdate,
};
