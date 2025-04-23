import { Collection, KeyedCollection, KeyedCollectionImpl } from './Collection';
import { IS_MAP_SYMBOL, isMap } from './predicates/isMap';
import { isOrdered } from './predicates/isOrdered';
import {
  DELETE,
  NOT_SET,

  MakeRef
} from './TrieUtils';

import { Iterator, iteratorValue, iteratorDone } from './Iterator';
import { sortFactory } from './Operations';
import assertNotInfinite from './utils/assertNotInfinite';
import { setIn } from './methods/setIn';
import { deleteIn } from './methods/deleteIn';
import { update } from './methods/update';
import { updateIn } from './methods/updateIn';
import { merge, mergeWith } from './methods/merge';
import { mergeDeep, mergeDeepWith } from './methods/mergeDeep';
import { mergeIn } from './methods/mergeIn';
import { mergeDeepIn } from './methods/mergeDeepIn';
import { withMutations } from './methods/withMutations';
import { asMutable } from './methods/asMutable';
import { asImmutable } from './methods/asImmutable';
import { wasAltered } from './methods/wasAltered';

import { OrderedMap } from './OrderedMap';

import {
  NodeArrayMap,
  NodeHashArrayMap,
  NodeHashCollision,
  NodeBitmapIndexed,
  NodeValue,
  nodeUpdate,
} from './Node';

export const Map = (value) =>
  value === undefined || value === null
    ? emptyMap()
    : isMap(value) && !isOrdered(value)
      ? value
      : emptyMap().withMutations((map) => {
          const iter = KeyedCollection(value);
          assertNotInfinite(iter.size);
          iter.forEach((v, k) => map.set(k, v));
        });

export class MapImpl extends KeyedCollectionImpl {
  create(value) {
    return Map(value);
  }

  toString() {
    return this.__toString('Map {', '}');
  }

  // @pragma Access

  get(k, notSetValue) {
    return this._root
      ? this._root.get(0, undefined, k, notSetValue)
      : notSetValue;
  }

  // @pragma Modification

  set(k, v) {
    return updateMap(this, k, v);
  }

  remove(k) {
    return updateMap(this, k, NOT_SET);
  }

  deleteAll(keys) {
    const collection = Collection(keys);

    if (collection.size === 0) {
      return this;
    }

    return this.withMutations((map) => {
      collection.forEach((key) => map.remove(key));
    });
  }

  clear() {
    if (this.size === 0) {
      return this;
    }
    if (this.__ownerID) {
      this.size = 0;
      this._root = null;
      this.__hash = undefined;
      this.__altered = true;
      return this;
    }
    return emptyMap();
  }

  // @pragma Composition

  sort(comparator) {
    // Late binding
    return OrderedMap(sortFactory(this, comparator));
  }

  sortBy(mapper, comparator) {
    // Late binding
    return OrderedMap(sortFactory(this, comparator, mapper));
  }

  map(mapper, context) {
    return this.withMutations((map) => {
      map.forEach((value, key) => {
        map.set(key, mapper.call(context, value, key, this));
      });
    });
  }

  // @pragma Mutability

  __iterator(type, reverse) {
    return new MapIterator(this, type, reverse);
  }

  __iterate(fn, reverse) {
    let iterations = 0;
    // eslint-disable-next-line @typescript-eslint/no-unused-expressions -- TODO enable eslint here
    this._root &&
      this._root.iterate((entry) => {
        iterations++;
        return fn(entry[1], entry[0], this);
      }, reverse);
    return iterations;
  }

  __ensureOwner(ownerID) {
    if (ownerID === this.__ownerID) {
      return this;
    }
    if (!ownerID) {
      if (this.size === 0) {
        return emptyMap();
      }
      this.__ownerID = ownerID;
      this.__altered = false;
      return this;
    }
    return makeMap(this.size, this._root, ownerID, this.__hash);
  }
}

Map.isMap = isMap;

const MapPrototype = MapImpl.prototype;
MapPrototype[IS_MAP_SYMBOL] = true;
MapPrototype[DELETE] = MapPrototype.remove;
MapPrototype.removeAll = MapPrototype.deleteAll;
MapPrototype.setIn = setIn;
MapPrototype.removeIn = MapPrototype.deleteIn = deleteIn;
MapPrototype.update = update;
MapPrototype.updateIn = updateIn;
MapPrototype.merge = MapPrototype.concat = merge;
MapPrototype.mergeWith = mergeWith;
MapPrototype.mergeDeep = mergeDeep;
MapPrototype.mergeDeepWith = mergeDeepWith;
MapPrototype.mergeIn = mergeIn;
MapPrototype.mergeDeepIn = mergeDeepIn;
MapPrototype.withMutations = withMutations;
MapPrototype.wasAltered = wasAltered;
MapPrototype.asImmutable = asImmutable;
MapPrototype['@@transducer/init'] = MapPrototype.asMutable = asMutable;
MapPrototype['@@transducer/step'] = function (result, arr) {
  return result.set(arr[0], arr[1]);
};
MapPrototype['@@transducer/result'] = function (obj) {
  return obj.asImmutable();
};

// #pragma Iterators
NodeArrayMap.prototype.iterate = NodeHashCollision.prototype.iterate =
  function (fn, reverse) {
    const entries = this.entries;
    for (let ii = 0, maxIndex = entries.length - 1; ii <= maxIndex; ii++) {
      if (fn(entries[reverse ? maxIndex - ii : ii]) === false) {
        return false;
      }
    }
  };

NodeBitmapIndexed.prototype.iterate = NodeHashArrayMap.prototype.iterate =
  function (fn, reverse) {
    const nodes = this.nodes;
    for (let ii = 0, maxIndex = nodes.length - 1; ii <= maxIndex; ii++) {
      const node = nodes[reverse ? maxIndex - ii : ii];
      if (node && node.iterate(fn, reverse) === false) {
        return false;
      }
    }
  };

// eslint-disable-next-line @typescript-eslint/no-unused-vars
NodeValue.prototype.iterate = function (fn, reverse) {
  return fn(this.entry);
};

class MapIterator extends Iterator {
  constructor(map, type, reverse) {
    super();

    this._type = type;
    this._reverse = reverse;
    this._stack = map._root && mapIteratorFrame(map._root);
  }

  next() {
    const type = this._type;
    let stack = this._stack;
    while (stack) {
      const node = stack.node;
      const index = stack.index++;
      let maxIndex;
      if (node.entry) {
        if (index === 0) {
          return mapIteratorValue(type, node.entry);
        }
      } else if (node.entries) {
        maxIndex = node.entries.length - 1;
        if (index <= maxIndex) {
          return mapIteratorValue(
            type,
            node.entries[this._reverse ? maxIndex - index : index]
          );
        }
      } else {
        maxIndex = node.nodes.length - 1;
        if (index <= maxIndex) {
          const subNode = node.nodes[this._reverse ? maxIndex - index : index];
          if (subNode) {
            if (subNode.entry) {
              return mapIteratorValue(type, subNode.entry);
            }
            stack = this._stack = mapIteratorFrame(subNode, stack);
          }
          continue;
        }
      }
      stack = this._stack = this._stack.__prev;
    }
    return iteratorDone();
  }
}

function mapIteratorValue(type, entry) {
  return iteratorValue(type, entry[0], entry[1]);
}

function mapIteratorFrame(node, prev) {
  return {
    node: node,
    index: 0,
    __prev: prev,
  };
}

function makeMap(size, root, ownerID, hash) {
  const map = Object.create(MapPrototype);
  map.size = size;
  map._root = root;
  map.__ownerID = ownerID;
  map.__hash = hash;
  map.__altered = false;
  return map;
}

let EMPTY_MAP;
export function emptyMap() {
  return EMPTY_MAP || (EMPTY_MAP = makeMap(0));
}

function updateMap(map, k, v) {
  let newRoot;
  let newSize;
  if (!map._root) {
    if (v === NOT_SET) {
      return map;
    }
    newSize = 1;
    newRoot = new NodeArrayMap(map.__ownerID, [[k, v]]);
  } else {
    const didChangeSize = MakeRef();
    const didAlter = MakeRef();
    newRoot = nodeUpdate(
      map._root,
      map.__ownerID,
      0,
      undefined,
      k,
      v,
      didChangeSize,
      didAlter
    );
    if (!didAlter.value) {
      return map;
    }
    newSize = map.size + (didChangeSize.value ? (v === NOT_SET ? -1 : 1) : 0);
  }
  if (map.__ownerID) {
    map.size = newSize;
    map._root = newRoot;
    map.__hash = undefined;
    map.__altered = true;
    return map;
  }
  return newRoot ? makeMap(newSize, newRoot) : emptyMap();
}
