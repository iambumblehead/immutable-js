import { hash } from './Hash';
import { is } from './is';

import {
  utilArrCopy,
  utilArrSetAt,
  utilArrSpliceIn,
  utilArrSpliceOut,
} from './util';

import {
  SHIFT,
  SIZE,
  MASK,
  NOT_SET,
  OwnerID,
  SetRef,
} from './TrieUtils';

const MAX_ARRAY_MAP_SIZE = SIZE / 4;
const MAX_BITMAP_INDEXED_SIZE = SIZE / 2;
const MIN_HASH_ARRAY_MAP_SIZE = SIZE / 4;

class NodeHashArrayMap {
  constructor(ownerID, count, nodes) {
    this.ownerID = ownerID;
    this.count = count;
    this.nodes = nodes;
  }

  get(shift, keyHash, key, notSetValue) {
    if (keyHash === undefined) {
      keyHash = hash(key);
    }
    const idx = (shift === 0 ? keyHash : keyHash >>> shift) & MASK;
    const node = this.nodes[idx];
    return node
      ? node.get(shift + SHIFT, keyHash, key, notSetValue)
      : notSetValue;
  }

  update(ownerID, shift, keyHash, key, value, didChangeSize, didAlter) {
    if (keyHash === undefined) {
      keyHash = hash(key);
    }
    const idx = (shift === 0 ? keyHash : keyHash >>> shift) & MASK;
    const removed = value === NOT_SET;
    const nodes = this.nodes;
    const node = nodes[idx];

    if (removed && !node) {
      return this;
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
      return this;
    }

    let newCount = this.count;
    if (!node) {
      newCount++;
    } else if (!newNode) {
      newCount--;
      if (newCount < MIN_HASH_ARRAY_MAP_SIZE) {
        return nodesPack(ownerID, nodes, newCount, idx);
      }
    }

    const isEditable = ownerID && ownerID === this.ownerID;
    const newNodes = utilArrSetAt(nodes, idx, newNode, isEditable);

    if (isEditable) {
      this.count = newCount;
      this.nodes = newNodes;
      return this;
    }

    return new NodeHashArrayMap(ownerID, newCount, newNodes);
  }
}

// was HashCollisionNode
class NodeHashCollision {
  constructor(ownerID, keyHash, entries) {
    this.ownerID = ownerID;
    this.keyHash = keyHash;
    this.entries = entries;
  }

  get(shift, keyHash, key, notSetValue) {
    const entries = this.entries;
    for (let ii = 0, len = entries.length; ii < len; ii++) {
      if (is(key, entries[ii][0])) {
        return entries[ii][1];
      }
    }
    return notSetValue;
  }

  update(ownerID, shift, keyHash, key, value, didChangeSize, didAlter) {
    if (keyHash === undefined) {
      keyHash = hash(key);
    }

    const removed = value === NOT_SET;

    if (keyHash !== this.keyHash) {
      if (removed) {
        return this;
      }
      SetRef(didAlter);
      SetRef(didChangeSize);
      return nodeMergeInto(this, ownerID, shift, keyHash, [key, value]);
    }

    const entries = this.entries;
    let idx = 0;
    const len = entries.length;
    for (; idx < len; idx++) {
      if (is(key, entries[idx][0])) {
        break;
      }
    }
    const exists = idx < len;

    if (exists ? entries[idx][1] === value : removed) {
      return this;
    }

    SetRef(didAlter);
    // eslint-disable-next-line @typescript-eslint/no-unused-expressions -- TODO enable eslint here
    (removed || !exists) && SetRef(didChangeSize);

    if (removed && len === 2) {
      return new NodeValue(ownerID, this.keyHash, entries[idx ^ 1]);
    }

    const isEditable = ownerID && ownerID === this.ownerID;
    const newEntries = isEditable ? entries : utilArrCopy(entries);

    if (exists) {
      if (removed) {
        // eslint-disable-next-line @typescript-eslint/no-unused-expressions -- TODO enable eslint here
        idx === len - 1
          ? newEntries.pop()
          : (newEntries[idx] = newEntries.pop());
      } else {
        newEntries[idx] = [key, value];
      }
    } else {
      newEntries.push([key, value]);
    }

    if (isEditable) {
      this.entries = newEntries;
      return this;
    }

    return new NodeHashCollision(ownerID, this.keyHash, newEntries);
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
}

// was NodeValue
class NodeValue {
  constructor(ownerID, keyHash, entry) {
    this.ownerID = ownerID;
    this.keyHash = keyHash;
    this.entry = entry;
  }

  get(shift, keyHash, key, notSetValue) {
    return is(key, this.entry[0]) ? this.entry[1] : notSetValue;
  }

  update(ownerID, shift, keyHash, key, value, didChangeSize, didAlter) {
    const removed = value === NOT_SET;
    const keyMatch = is(key, this.entry[0]);
    if (keyMatch ? value === this.entry[1] : removed) {
      return this;
    }

    SetRef(didAlter);

    if (removed) {
      SetRef(didChangeSize);
      return; // undefined
    }

    if (keyMatch) {
      if (ownerID && ownerID === this.ownerID) {
        this.entry[1] = value;
        return this;
      }
      return new NodeValue(ownerID, this.keyHash, [key, value]);
    }

    SetRef(didChangeSize);
    return nodeMergeInto(this, ownerID, shift, hash(key), [key, value]);
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
}

const popCount = (x) => {
  x -= (x >> 1) & 0x55555555;
  x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
  x = (x + (x >> 4)) & 0x0f0f0f0f;
  x += x >> 8;
  x += x >> 16;
  return x & 0x7f;
};

class NodeBitmapIndexed {
  constructor(ownerID, bitmap, nodes) {
    this.ownerID = ownerID;
    this.bitmap = bitmap;
    this.nodes = nodes;
  }

  get(shift, keyHash, key, notSetValue) {
    if (keyHash === undefined) {
      keyHash = hash(key);
    }
    const bit = 1 << ((shift === 0 ? keyHash : keyHash >>> shift) & MASK);
    const bitmap = this.bitmap;
    return (bitmap & bit) === 0
      ? notSetValue
      : this.nodes[popCount(bitmap & (bit - 1))].get(
          shift + SHIFT,
          keyHash,
          key,
          notSetValue
        );
  }

  update(ownerID, shift, keyHash, key, value, didChangeSize, didAlter) {
    if (keyHash === undefined) {
      keyHash = hash(key);
    }
    const keyHashFrag = (shift === 0 ? keyHash : keyHash >>> shift) & MASK;
    const bit = 1 << keyHashFrag;
    const bitmap = this.bitmap;
    const exists = (bitmap & bit) !== 0;

    if (!exists && value === NOT_SET) {
      return this;
    }

    const idx = popCount(bitmap & (bit - 1));
    const nodes = this.nodes;
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
      return this;
    }

    if (!exists && newNode && nodes.length >= MAX_BITMAP_INDEXED_SIZE) {
      return nodesExpand(ownerID, nodes, bitmap, keyHashFrag, newNode);
    }

    if (
      exists &&
      !newNode &&
      nodes.length === 2 &&
      nodeIsLeaf(nodes[idx ^ 1])
    ) {
      return nodes[idx ^ 1];
    }

    if (exists && newNode && nodes.length === 1 && nodeIsLeaf(newNode)) {
      return newNode;
    }

    const isEditable = ownerID && ownerID === this.ownerID;
    const newBitmap = exists ? (newNode ? bitmap : bitmap ^ bit) : bitmap | bit;
    const newNodes = exists
      ? newNode
        ? utilArrSetAt(nodes, idx, newNode, isEditable)
        : utilArrSpliceOut(nodes, idx, isEditable)
      : utilArrSpliceIn(nodes, idx, newNode, isEditable);

    if (isEditable) {
      this.bitmap = newBitmap;
      this.nodes = newNodes;
      return this;
    }

    return new NodeBitmapIndexed(ownerID, newBitmap, newNodes);
  }
}

class NodeArrayMap {
  constructor(ownerID, entries) {
    this.ownerID = ownerID;
    this.entries = entries;
  }

  get(shift, keyHash, key, notSetValue) {
    const entries = this.entries;
    for (let ii = 0, len = entries.length; ii < len; ii++) {
      if (is(key, entries[ii][0])) {
        return entries[ii][1];
      }
    }
    return notSetValue;
  }

  update(ownerID, shift, keyHash, key, value, didChangeSize, didAlter) {
    const removed = value === NOT_SET;

    const entries = this.entries;
    let idx = 0;
    const len = entries.length;
    for (; idx < len; idx++) {
      if (is(key, entries[idx][0])) {
        break;
      }
    }
    const exists = idx < len;

    if (exists ? entries[idx][1] === value : removed) {
      return this;
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

    const isEditable = ownerID && ownerID === this.ownerID;
    const newEntries = isEditable ? entries : utilArrCopy(entries);

    if (exists) {
      if (removed) {
        // eslint-disable-next-line @typescript-eslint/no-unused-expressions -- TODO enable eslint here
        idx === len - 1
          ? newEntries.pop()
          : (newEntries[idx] = newEntries.pop());
      } else {
        newEntries[idx] = [key, value];
      }
    } else {
      newEntries.push([key, value]);
    }

    if (isEditable) {
      this.entries = newEntries;
      return this;
    }

    return new NodeArrayMap(ownerID, newEntries);
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
  NodeHashArrayMap,
  NodeHashCollision,
  NodeBitmapIndexed,
  NodeValue,
  nodesExpand,
  nodesPack,
  nodesCreate,
  nodeMergeInto,
  nodeIsLeaf,
  nodeUpdate,
};
