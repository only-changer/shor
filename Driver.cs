using Microsoft.Quantum.Simulation.Core;
using Microsoft.Quantum.Simulation.Simulators;
using System;

namespace Quantum.shor
{
    class Driver
    {
        static Random rnd = new Random();

        static void Main(string[] args)
        {
            Console.WriteLine("请输入你要分解的数...");
            int factorme = Convert.ToInt32(Console.ReadLine());
            using (var sim = new QuantumSimulator())
            {
                int cnt = 0;
                while (true)
                {
                    ++cnt;

                    var testradix = ChooseRandomCoprime(factorme);

                    Console.WriteLine("Starting Quantum Routine: radix = {0}, modulus = {1}", testradix, factorme);
                    long res = shor.Run(sim, testradix, factorme).Result;
                    Console.WriteLine("Result {0}", res);
                    if ((res != 1) && (res != factorme - 1) && (res * res % factorme == 1))
                    {
                        Console.WriteLine("Factors Found: {0} x {1} = {2}", Gcd(res + 1, factorme), factorme / Gcd(res + 1, factorme), factorme);
                        break;
                    }

                    if (cnt > factorme)
                    {
                        Console.WriteLine("未发现因子，该数可能为质数...");
                        break;
                    }
                } 
            }
            Console.WriteLine("按任意键继续...");
            Console.ReadKey();
        }

        static long Gcd(long x, long y)
        {
            return y == 0 ? x : Gcd(y, x % y);
        }

        static int ChooseRandomCoprime(int x)
        {
            int y = rnd.Next(x/3, x - 2);
            return Gcd(x, y) == 1 ? y : ChooseRandomCoprime(x);
        }
    }
}