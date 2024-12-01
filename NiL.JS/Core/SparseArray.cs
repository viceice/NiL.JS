using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading.Tasks;

namespace NiL.JS.Core;

[DebuggerDisplay("Count = {Count}")]
public sealed class SparseArray<TValue> : IList<TValue>, IDictionary<int, TValue>, ICloneable
{
    [StructLayout(LayoutKind.Sequential, Pack = 1)]
    private struct NavyItem
    {
        public uint index;
        public ushort zeroContinue;
        public ushort oneContinue;

        public override string ToString()
        {
            return index + "[" + zeroContinue + ";" + oneContinue + "]";
        }
    }

    private const int SegmentSize = 16384;

    private static TValue _fictive;

    private uint _pseudoLength;

    private NavyItem[] _segmentsNavyData;
    private int _segmentsCount;

    private NavyItem[][] _navyData;
    private TValue[][] _values;
    private ushort[] _used;

    [CLSCompliant(false)]
    public uint Length => _pseudoLength;

    public SparseArray()
    {
        _segmentsNavyData = [];
        _values = [];
        _navyData = [];
        _used = [];
    }

    public SparseArray(TValue[] values)
    {
        _segmentsNavyData = [];
        _values = [];
        _navyData = [];
        _used = [];

        for (var i = 0; i < values.Length; i++)
            this[i] = values[i];
    }

    #region Члены IList<TValue>

    public int IndexOf(TValue item)
    {
        for (var i = 0; i < _pseudoLength; i++)
        {
            if (Equals(this[i], item))
                return i;
        }

        return -1;
    }

    void IList<TValue>.Insert(int index, TValue item)
    {
        throw new NotImplementedException();
    }

    /// <summary>
    /// If "index" not equal "Length - 1", method will fail
    /// </summary>
    /// <param name="index">Index of item for removing</param>
    public void RemoveAt(int index)
    {
        if (_pseudoLength == 0 || index != (int)(_pseudoLength - 1))
            throw new InvalidOperationException();

        this[(int)(_pseudoLength - 1)] = default!;
        _pseudoLength--;
    }

    public ref TValue GetExistent(int index)
    {
        return ref TryGetInternalForWrite((uint)index, out _);
    }

    internal ref TValue TryGetInternalForRead(uint index, out bool got)
    {
        var virtualSegmentIndex = index / SegmentSize;
        var realSegmentIndex = segmentIndexRecalc(virtualSegmentIndex, true);

        if (realSegmentIndex < 0 || _navyData.Length <= realSegmentIndex)
        {
            got = false;
            _fictive = default;
            return ref _fictive;
        }

        if (_navyData[realSegmentIndex].Length == 0)
        {
            var values = _values[realSegmentIndex];
            var itemIndex = index & (SegmentSize - 1);

            if (itemIndex >= values.Length)
            {
                got = false;
                _fictive = default;
                return ref _fictive;
            }

            got = true;
            return ref values[itemIndex];
        }

        ref var result = ref getFromTree(index, true, out got, realSegmentIndex);
        return ref result;
    }

    internal ref TValue TryGetInternalForWrite(uint index, out bool got)
    {
        var virtaulSegmentIndex = index / SegmentSize;
        var realSegmentIndex = segmentIndexRecalc(virtaulSegmentIndex, false);

        if (_navyData.Length <= realSegmentIndex)
        {
            resizeL0(realSegmentIndex);
        }

        if (_navyData[realSegmentIndex].Length == 0)
        {
            var values = _values[realSegmentIndex];
            var itemIndex = (int)index & (SegmentSize - 1);

            if (itemIndex >= values.Length)
            {
                if (itemIndex <= values.Length + 4)
                {
                    Array.Resize(ref values, Math.Min(SegmentSize, Math.Max(values.Length * 2, 8)));

                    _values[realSegmentIndex] = values;
                }
                else
                {
                    rebuildSegmentToSparse(realSegmentIndex, values);

                    return ref getFromTree(index, false, out got, realSegmentIndex);
                }
            }

            if (_pseudoLength <= index)
                _pseudoLength = index + 1;

            got = true;
            return ref values[itemIndex];
        }

        return ref getFromTree(index, false, out got, realSegmentIndex);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private void rebuildSegmentToSparse(int realSegmentIndex, TValue[] values)
    {
        var oldLen = values.Length;
        var len = values.Length;

        if (values.Length == 0)
            len = 2;

        if (values.Length != len)
        {
            Array.Resize(ref values, len);
            _values[realSegmentIndex] = values;
        }

        _navyData[realSegmentIndex] = new NavyItem[len];

        var bias = _segmentsNavyData[realSegmentIndex].index * SegmentSize;

        if (typeof(TValue).IsClass)
        {
            for (var valueIndex = 0; valueIndex < oldLen; valueIndex++)
            {
                if (values[valueIndex] is not null)
                {
                    var value = values[valueIndex];
                    values[valueIndex] = default;
                    getFromTree((uint)(valueIndex + bias), false, out _, realSegmentIndex) = value;
                }
            }
        }
        else
        {
            for (var valueIndex = 0; valueIndex < oldLen; valueIndex++)
            {
                var value = values[valueIndex];
                values[valueIndex] = default;
                getFromTree((uint)(valueIndex + bias), false, out _, realSegmentIndex) = value;
            }
        }
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private void resizeL0(int newRealSegmentsCount)
    {
        Array.Resize(ref _navyData, newRealSegmentsCount is 0 ? 1 : 2 << NumberUtils.IntLog(newRealSegmentsCount));
        Array.Resize(ref _segmentsNavyData, _navyData.Length);
        Array.Resize(ref _values, _navyData.Length);
        Array.Resize(ref _used, _navyData.Length);

        for (var i = _navyData.Length - 1; i >= 0 && _navyData[i] is null; i--)
            _navyData[i] = [];

        for (var i = _values.Length - 1; i >= 0 && _values[i] is null; i--)
        {
            _values[i] = [];
        }
    }


    private enum FindNearestMode { NotLess, NotMore }
    private (int realSegmentIndex, int virtualSegmentIndex, int realItemIndex) findNearest(long index, FindNearestMode mode)
    {
        var navy = _segmentsNavyData;

        if (navy.Length == 0)
            return (-1, -1, -1);

        var virtualSegmentIndex = (uint)index / SegmentSize;
        var mask = (int)((1L << 31) / SegmentSize);
        var firstTry = _segmentsCount > index;
        var i = firstTry ? (int)index : 0;
        int nextIndex;
        var realSegmentIndex = -1;
        var alterI = -1;

        if (mode is FindNearestMode.NotLess)
        {
            while (true)
            {
                ref var navyItem = ref navy[i];
                if (navyItem.index == virtualSegmentIndex)
                {
                    realSegmentIndex = i;

                    if (_navyData[realSegmentIndex].Length == 0)
                    {
                        if (_values[realSegmentIndex].Length > (int)(index & (SegmentSize - 1)))
                        {
                            return (realSegmentIndex, (int)navyItem.index, (int)(index & (SegmentSize - 1)));
                        }
                    }
                    else
                    {
                        mask = SegmentSize >> 1;
                        var n = _navyData[realSegmentIndex][0];
                        var itemIndex = 0;
                        var nestedAlterI = -1;
                        while (true)
                        {
                            if (n.index >= index)
                                return (realSegmentIndex, (int)navyItem.index, itemIndex);

                            itemIndex = (index & mask) == 0 ? n.zeroContinue : n.oneContinue;

                            if (itemIndex == 0)
                            {
                                if (n.oneContinue == 0)
                                {
                                    if (nestedAlterI == -1)
                                        break;

                                    mask = 0;
                                    n = _navyData[realSegmentIndex][nestedAlterI];
                                    itemIndex = nestedAlterI;
                                    nestedAlterI = -1;
                                    continue;
                                }

                                itemIndex = n.oneContinue;
                                mask = 0;
                            }

                            if (itemIndex != n.oneContinue && n.oneContinue != 0)
                                nestedAlterI = n.oneContinue;

                            mask >>= 1;
                            n = _navyData[realSegmentIndex][itemIndex];
                        }
                    }
                }
                
                if (firstTry)
                {
                    firstTry = false;
                    i = 0;
                    continue;
                }

                if (navyItem.index > virtualSegmentIndex)
                {
                    // дальнейшее продвижение будет только увеличивать индекс
                    virtualSegmentIndex = navyItem.index;
                    realSegmentIndex = i;
                    return (realSegmentIndex, (int)virtualSegmentIndex, 0);
                }

                var isZero = (virtualSegmentIndex & mask) == 0;
                nextIndex = isZero ? navyItem.zeroContinue : navyItem.oneContinue;

                if (nextIndex == 0)
                {
                    if (navyItem.oneContinue == 0)
                    {
                        if (alterI == -1)
                            return (-1, -1, -1);

                        mask = 0;
                        i = alterI;
                        continue;
                    }
                    else
                    {
                        mask = 0;
                        nextIndex = navyItem.oneContinue;
                    }
                }

                if (isZero && navyItem.oneContinue != 0)
                    alterI = navyItem.oneContinue;

                i = nextIndex;
                mask >>= 1;
            }
        }
        else
        {
            while (true)
            {
                ref var navyItem = ref navy[i];
                if (navyItem.index == virtualSegmentIndex)
                {
                    realSegmentIndex = i;

                    if (_navyData[realSegmentIndex].Length == 0)
                    {
                        return (realSegmentIndex, (int)navyItem.index, Math.Min(_values[realSegmentIndex].Length - 1, (int)(index & (SegmentSize - 1))));
                    }
                    else
                    {
                        mask = SegmentSize >> 1;
                        var n = _navyData[realSegmentIndex][0];
                        var itemIndex = 0;
                        while (true)
                        {
                            if (n.index == index)
                                return (realSegmentIndex, (int)navyItem.index, itemIndex);

                            if (n.index > index)
                                return (-1, -1, -1);

                            itemIndex = (index & mask) == 0 ? n.zeroContinue : n.oneContinue;

                            if (itemIndex == 0)
                            {
                                if (n.zeroContinue == 0)
                                    return (realSegmentIndex, (int)navyItem.index, itemIndex);

                                itemIndex = n.zeroContinue;
                                mask = int.MaxValue;
                            }

                            mask >>= 1;
                            n = _navyData[realSegmentIndex][itemIndex];
                        }
                    }
                }
                
                if (firstTry)
                {
                    firstTry = false;
                    i = 0;
                    continue;
                }

                if (navyItem.index > virtualSegmentIndex)
                {
                    return (-1, -1, -1);
                }

                var isZero = (virtualSegmentIndex & mask) == 0;
                nextIndex = isZero ? navyItem.zeroContinue : navyItem.oneContinue;

                if (nextIndex == 0)
                {
                    if (isZero)
                    {
                        if (alterI == -1)
                            return (-1, -1, -1);

                        mask = int.MaxValue;
                        i = alterI;

                        continue;
                    }
                }

                if (navy[nextIndex].index > virtualSegmentIndex
                    || (_navyData[nextIndex].Length > 0 && _navyData[nextIndex][0].index > index))
                {
                    realSegmentIndex = i;

                    if (_navyData[realSegmentIndex].Length == 0)
                        return (realSegmentIndex, (int)navyItem.index, _values[realSegmentIndex].Length - 1);
                    else
                    {
                        var n = _navyData[realSegmentIndex][0];
                        var itemIndex = 0;
                        while (true)
                        {
                            if (n.oneContinue != 0)
                                n = _navyData[realSegmentIndex][itemIndex = n.oneContinue];
                            else if (n.zeroContinue != 0)
                                n = _navyData[realSegmentIndex][itemIndex = n.zeroContinue];
                            else
                                break;
                        }

                        return (realSegmentIndex, (int)navyItem.index, itemIndex);
                    }
                }

                if (!isZero && navyItem.zeroContinue != 0)
                    alterI = navyItem.zeroContinue;

                i = nextIndex;
                mask >>= 1;
            }
        }
    }

    private int segmentIndexRecalc(uint index, bool forRead)
    {
        var navy = _segmentsNavyData;

        if (navy.Length == 0)
        {
            if (forRead)
                return -1;

            _segmentsNavyData = [new() { index = index }];
            _segmentsCount = 1;
            return 0;
        }

        if (index < _segmentsCount && navy[index].index == index)
            return (int)index;

        var mask = (int)((1L << 31) / SegmentSize);
        var i = 0;
        int nextIndex;
        while (true)
        {
            var navyItem = navy[i];
            if (navyItem.index == index)
                return i;

            if (navyItem.index > index)
            {
                if (forRead)
                    return -1;

                var oldIndex = navyItem.index;
                var oldNavyData = _navyData[i];
                var oldValues = _values[i];
                var oldUsed = _used[i];

                _navyData[i] = [];
                _values[i] = [];
                _used[i] = 0;
                navy[i].index = index;

                nextIndex = segmentIndexRecalc(oldIndex, false);

                _segmentsNavyData[nextIndex].index = oldIndex;
                _navyData[nextIndex] = oldNavyData;
                _values[nextIndex] = oldValues;
                _used[nextIndex] = oldUsed;

                return i;
            }

            var isNotZero = (index & mask) != 0;
            nextIndex = isNotZero ? navyItem.oneContinue : navyItem.zeroContinue;

            if (nextIndex == 0)
            {
                if (forRead)
                    return -1;

                _segmentsCount = checked((ushort)(_segmentsCount + 1));
                nextIndex = _segmentsCount - 1;

                if (isNotZero)
                    navy[i].oneContinue = (ushort)nextIndex;
                else
                    navy[i].zeroContinue = (ushort)nextIndex;

                if (nextIndex >= navy.Length)
                {
                    var newSize = nextIndex * 2;
                    resizeL0(newSize);

                    navy = _segmentsNavyData;
                }

                navy[nextIndex].index = index;
            }

            i = nextIndex;
            mask >>= 1;
        }
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private ref TValue getFromTree(uint index, bool forRead, out bool got, int realSegmentIndex)
    {
        var mask = SegmentSize >> 1;
        var values = _values[realSegmentIndex];
        var navy = _navyData[realSegmentIndex];

        var i = (int)index & (SegmentSize - 1);

        if (i < navy.Length && navy[i].index == index)
        {
            if (!forRead && i == 0 && _used[realSegmentIndex] == 0)
            {
                _used[realSegmentIndex] = 1;
            }

            got = true;
            return ref values[i];
        }

        i = 0;

        ushort ni;
        while (true)
        {
            ref var navyItem = ref navy[i];
            if (navyItem.index < index)
            {
                var isNotZero = (index & mask) != 0;
                ni = isNotZero ? navyItem.oneContinue : navyItem.zeroContinue;

                if (ni == 0)
                {
                    if (forRead)
                    {
                        got = false;
                        _fictive = default;
                        return ref _fictive;
                    }

                    if (_pseudoLength <= index)
                        _pseudoLength = index + 1;

                    ni = _used[realSegmentIndex]++;

                    if (isNotZero)
                        navyItem.oneContinue = ni;
                    else
                        navyItem.zeroContinue = ni;

                    if (ni >= navy.Length)
                    {
                        var newSize = ni * 2;

                        Array.Resize(ref _navyData[realSegmentIndex], newSize);
                        Array.Resize(ref _values[realSegmentIndex], newSize);

                        navy = _navyData[realSegmentIndex];
                        values = _values[realSegmentIndex];
                    }

                    navy[ni].index = index;
                    got = true;
                    return ref values[ni];
                }

                i = ni;
                mask >>= 1;
            }
            else if (navyItem.index > index)
            {
                if (forRead)
                {
                    got = false;
                    _fictive = default;
                    return ref _fictive;
                }

                var oldIndex = navyItem.index;
                var oldValue = values[i];

                navyItem.index = index;

                if (oldIndex < _pseudoLength)
                    this[(int)oldIndex] = oldValue!;

                values = _values[realSegmentIndex];
                values[i] = default!;

                got = true;
                return ref values[i];
            }
            else
            {
                if (!forRead && _pseudoLength <= index)
                    _pseudoLength = index + 1;

                got = true;
                return ref values[i];
            }
        }
    }

    public TValue this[int index]
    {
        get
        {
            ref var r = ref TryGetInternalForRead((uint)index, out var got);

            if (got)
                return r;

            return default;
        }
        set
        {
            bool isDefault = value is null; // структуры мы будем записывать, иначе пришлось бы вызывать тяжелые операции сравнения.

            if (isDefault)
            {
                if (_pseudoLength <= (uint)index)
                    _pseudoLength = (uint)index + 1;
                else
                {
                    ref var maybeExists = ref TryGetInternalForRead((uint)index, out var got);
                    if (got)
                        maybeExists = default;
                }
            }
            else
                TryGetInternalForWrite((uint)index, out _) = value;
        }
    }

    #endregion

    #region Члены ICollection<TValue>

    public void Add(TValue item)
    {
        if (_pseudoLength == uint.MaxValue)
            throw new InvalidOperationException();

        this[(int)_pseudoLength++] = item;
    }

    public void TrimLength()
    {
        var coord = findNearest(_pseudoLength - 1, FindNearestMode.NotMore);
        var externalIndex = getExternalIndex(coord);
        _pseudoLength = (uint)externalIndex + 1;
    }

    private long getExternalIndex((int realSegmentIndex, int virtualSegmentIndex, int itemIndex) coord)
    {
        if (coord.itemIndex == -1)
            return -1;

        var navyItems = _navyData[coord.realSegmentIndex];
        if (navyItems.Length != 0)
            return navyItems[coord.itemIndex].index;

        var externalIndex = coord.virtualSegmentIndex * SegmentSize + (uint)coord.itemIndex;
        return externalIndex;
    }

    public void Clear()
    {
        _segmentsNavyData = [];
        _values = [];
        _navyData = [];
        _used = [];
        _pseudoLength = 0;
    }

    public bool Contains(TValue item)
    {
        return IndexOf(item) != -1;
    }

    public void CopyTo(TValue[] array, int arrayIndex)
    {
        if (array == null)
            throw new NullReferenceException();
        if (arrayIndex < 0)
            throw new ArgumentOutOfRangeException();
        if (Math.Min(_pseudoLength, int.MaxValue) - arrayIndex > array.Length)
            throw new ArgumentOutOfRangeException();

        for (var i = Math.Min(_pseudoLength, int.MaxValue) + arrayIndex; i-- > arrayIndex;)
        {
            array[i] = default;
        }

        foreach (var v in ForwardOrder)
        {
            if (v.Key >= 0)
                array[v.Key + arrayIndex] = v.Value;
        }
    }

    int ICollection<TValue>.Count
    {
        get { return (int)_pseudoLength; }
    }

    public bool IsReadOnly
    {
        get { return false; }
    }

    public bool Remove(TValue item)
    {
        throw new NotImplementedException();
    }

    #endregion

    #region Члены IEnumerable<TValue>

    public IEnumerator<TValue> GetEnumerator()
    {
        for (var i = 0u; i < _pseudoLength; i++)
            yield return this[(int)i];
    }

    #endregion

    #region Члены IEnumerable

    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator()
    {
        return GetEnumerator();
    }

    #endregion

    /// <summary>
    ///
    /// </summary>
    /// <param name="index"></param>
    /// <returns>Zero if the requested index does not Exists</returns>
    public long NearestNotLess(long index, out TValue value)
    {
        if (_pseudoLength < index)
        {
            value = default;
            return -1;
        }

        var coord = findNearest(index, FindNearestMode.NotLess);

        if (coord.realItemIndex == -1)
        {
            value = default;
            return -1;
        }

        value = _values[coord.realSegmentIndex][coord.realItemIndex];
        var externalIndex = getExternalIndex(coord);
        return externalIndex;
    }

    public long NearestNotMore(long index, out TValue value)
    {
        var coord = findNearest(index, FindNearestMode.NotMore);

        if (coord.realItemIndex == -1)
        {
            value = default;
            return -1;
        }

        value = _values[coord.realSegmentIndex][coord.realItemIndex];
        var externalIndex = getExternalIndex(coord);
        return externalIndex;
    }

    public IEnumerable<int> KeysForwardOrder => ForwardOrder.Select(x => x.Key);

    public IEnumerable<KeyValuePair<int, TValue>> ForwardOrder
    {
        get
        {
            var index = 0L;

            while (index < _pseudoLength)
            {
                index = NearestNotLess(index, out var value);

                if (index < 0)
                    break;

                yield return new KeyValuePair<int, TValue>((int)index, value);

                index++;
            }

            if (index < _pseudoLength)
                yield return new KeyValuePair<int, TValue>((int)_pseudoLength - 1, default);
        }
    }

    public IEnumerable<KeyValuePair<int, TValue>> Unordered
    {
        get
        {
            for (var i = 0; i < _navyData.Length; i++)
            {
                if (_navyData[i].Length != 0)
                {
                    for (var j = 0; j < _used[i]; j++)
                    {
                        yield return new KeyValuePair<int, TValue>(_navyData[i].Length is 0 ? i * SegmentSize + j : (int)_navyData[i][j].index, _values[i][j]!);
                    }
                }
                else
                {
                    for (var j = 0; j < _values[i].Length; j++)
                    {
                        if (i * SegmentSize + j >= _pseudoLength)
                            break;

                        yield return new KeyValuePair<int, TValue>(i * SegmentSize + j, _values[i][j]!);
                    }
                }
            }
        }
    }

    public IEnumerable<int> KeysReverseOrder
    {
        get
        {
            if (_pseudoLength == 0)
                yield break;

            long index = (long)_pseudoLength - 1;

            var lastYielded = false;
            var zeroYielded = index == 0;

            while (index >= 0)
            {
                var coord = findNearest(index, FindNearestMode.NotMore);
                index = getExternalIndex(coord);

                if (!lastYielded)
                {
                    if (index < _pseudoLength - 1)
                        yield return (int)(_pseudoLength - 1);

                    lastYielded = true;
                }

                if (index < 0)
                    break;

                if (index == 0)
                    zeroYielded = true;

                yield return (int)index;

                index--;
            }

            if (!zeroYielded)
                yield return 0;
        }
    }

    public IEnumerable<KeyValuePair<int, TValue>> ReverseOrder
    {
        get
        {
            if (_pseudoLength == 0)
                yield break;

            long index = (long)_pseudoLength - 1;

            var lastYielded = false;
            var zeroYielded = index == 0;

            while (index >= 0)
            {
                index = NearestNotMore(index, out var value);

                if (!lastYielded)
                {
                    if (index < _pseudoLength - 1)
                        yield return new KeyValuePair<int, TValue>((int)(_pseudoLength - 1), default);

                    lastYielded = true;
                }

                if (index < 0)
                    break;

                if (index == 0)
                    zeroYielded = true;

                yield return new KeyValuePair<int, TValue>((int)index, value);

                index--;
            }

            if (!zeroYielded)
                yield return new KeyValuePair<int, TValue>(0, default);
        }
    }

    public ICollection<int> Keys => KeysForwardOrder.ToList();

    public ICollection<TValue> Values => ForwardOrder.Select(x => x.Value).ToList();

    public int Count => (int)Length;

    public void Add(int key, TValue value)
    {
        if (NearestNotLess(key, out _) == key)
            throw new InvalidOperationException();

        this[key] = value;
    }

    public bool ContainsKey(int key)
    {
        return NearestNotLess(key, out _) == key;
    }

    public bool Remove(int key)
    {
        if (key >= _pseudoLength)
            return false;

        if (key < _pseudoLength)
            this[key] = default;

        if (key == _pseudoLength - 1)
            _pseudoLength--;

        return true;
    }

    public bool TryGetValue(int key, [MaybeNullWhen(false)] out TValue value)
    {
        if (_pseudoLength <= key)
        {
            value = default;
            return false;
        }

        value = this[key];
        return true;
    }

    public void Add(KeyValuePair<int, TValue> item)
    {
        Add(item.Key, item.Value);
    }

    public bool Contains(KeyValuePair<int, TValue> item)
    {
        return Equals(this[item.Key], item.Value);
    }

    public void CopyTo(KeyValuePair<int, TValue>[] array, int arrayIndex)
    {
        throw new NotImplementedException();
    }

    public bool Remove(KeyValuePair<int, TValue> item)
    {
        if (Contains(item))
            return Remove(item.Key);

        return false;
    }

    IEnumerator<KeyValuePair<int, TValue>> IEnumerable<KeyValuePair<int, TValue>>.GetEnumerator()
    {
        foreach (var item in ForwardOrder)
            yield return item;
    }

    public object Clone()
    {
        var result = new SparseArray<TValue>();

        result._navyData = new NavyItem[_navyData.Length][];
        for (var i = 0; i < _navyData.Length; i++)
        {
            result._navyData[i] = _navyData[i]?.Clone() as NavyItem[];
        }

        result._values = new TValue[_values.Length][];
        for (var i = 0; i < _values.Length; i++)
        {
            result._values[i] = _values[i]?.Clone() as TValue[];
        }

        result._used = _used.Clone() as ushort[];

        result._pseudoLength = _pseudoLength;

        result._segmentsCount = _segmentsCount;

        result._segmentsNavyData = _segmentsNavyData.Clone() as NavyItem[];

        return result;
    }
}