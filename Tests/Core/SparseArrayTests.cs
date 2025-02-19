using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Reflection;
using System.Text;
using System.Threading.Tasks;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using NiL.JS.Core;

namespace Tests.Core
{
    [TestClass]
    public class SparseArrayTests
    {
        [TestMethod]
        public void DirectOrderShouldWorkCorrectlyInSparseMode()
        {
            var sparseArray = new SparseArray<int>(ArrayMode.Sparse);

            unchecked
            {
                for (var i = 32; i >= 0; i--)
                    sparseArray[i] = i;
            }

            var output = sparseArray.DirectOrder.ToArray();
            for (var i = 0; i <= 32; i++)
                Assert.AreEqual(i, output[i].Value);
        }

        [TestMethod]
        public void DirectOrderShouldWorkCorrectlyInSparseMode2()
        {
            var sparseArray = new SparseArray<int>(ArrayMode.Sparse);

            unchecked
            {
                sparseArray[0] = 1;
                sparseArray[1] = 2;
                sparseArray[10000] = 10000;
            }

            var output = sparseArray.DirectOrder.ToArray();
            Assert.AreEqual(1, output[0].Value);
            Assert.AreEqual(2, output[1].Value);
            Assert.AreEqual(10000, output[2].Value);
        }

        [TestMethod]
        public void DirectOrderShouldWorkCorrectlyInSparseMode3()
        {
            var sparseArray = new SparseArray<int>(ArrayMode.Sparse);

            unchecked
            {
                sparseArray[(int)4294967294] = 2;

                sparseArray[(int)4294967200] = 3;
                sparseArray[(int)4294967201] = 4;
                sparseArray[(int)4294967202] = 5;
            }

            var output = sparseArray.DirectOrder.ToArray();
            Assert.AreEqual(3, output[0].Value);
            Assert.AreEqual(4, output[1].Value);
            Assert.AreEqual(5, output[2].Value);
            Assert.AreEqual(2, output[3].Value);
        }

        [TestMethod]
        public void ReverseOrderShouldWorkCorrectlyInSparseMode()
        {
            var sparseArray = new SparseArray<int>(ArrayMode.Sparse);

            unchecked
            {
                for (var i = 32; i >= 0; i--)
                    sparseArray[i] = i;
            }

            var output = sparseArray.ReversOrder.ToArray();
            for (var i = 0; i <= 32; i++)
                Assert.AreEqual(32 - i, output[i].Value);
        }

        [Ignore]
        [TestMethod]
        public void PerformanceTest()
        {
            //Func<SortedDictionary<int, int>> storage = () => new SortedDictionary<int, int>();
            Func<SparseArray<int>> storage = () => new SparseArray<int>();
            //Func<Dictionary<int, int>> storage = () => new Dictionary<int, int>();

            Console.WriteLine(storage.GetMethodInfo().ReturnType);

            var sparseArray = storage();
            var random = new Random(0x1234);

            var writeRounds = 1;
            var writeCount = 1000000;
            var readRounds = 1;
            var readCount = 1000000;

            var sw = Stopwatch.StartNew();
            for (var r = 0; r < writeRounds; r++)
                for (var i = 0; i < writeCount; i++)
                    sparseArray[random.Next(1000000)] = i;
            Console.WriteLine("random write " + writeRounds + "*" + writeCount + ": " + sw.Elapsed);

            random = new Random(0x1234);

            sw.Restart();
            for (var r = 0; r < readRounds; r++)
                for (var i = 0; i < readCount; i++)
                    if (!sparseArray.TryGetValue(random.Next(1000000), out _))
                        System.Diagnostics.Debugger.Break();
            Console.WriteLine("random read  " + readRounds + "*" + readCount + ": " + sw.Elapsed);

            sparseArray = storage();

            sw.Restart();
            for (var r = 0; r < writeRounds; r++)
                for (var i = 0; i < writeCount; i++)
                    sparseArray[i * 10] = i;
            Console.WriteLine("step write    " + writeRounds + "*" + writeCount + ": " + sw.Elapsed);

            random = new Random(0x1234);

            sw.Restart();
            for (var r = 0; r < readRounds; r++)
                for (var i = 0; i < readCount; i++)
                    sparseArray.TryGetValue(i * 10, out _);
            Console.WriteLine("step read     " + readRounds + "*" + readCount + ": " + sw.Elapsed);

            sparseArray = storage();

            sw.Restart();
            for (var r = 0; r < writeRounds; r++)
                for (var i = 0; i < writeCount; i++)
                    sparseArray[i] = i;
            Console.WriteLine("seq write    " + writeRounds + "*" + writeCount + ": " + sw.Elapsed);

            random = new Random(0x1234);

            sw.Restart();
            for (var r = 0; r < readRounds; r++)
                for (var i = 0; i < readCount; i++)
                    sparseArray.TryGetValue(i, out _);
            Console.WriteLine("seq read     " + readRounds + "*" + readCount + ": " + sw.Elapsed);
        }
    }
}
