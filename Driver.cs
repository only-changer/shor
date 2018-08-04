using Microsoft.Quantum.Simulation.Core;
using Microsoft.Quantum.Simulation.Simulators;
using System;

// Full credit to this awesome blog post I used http://algassert.com/post/1718

namespace Quantum.ShorQsharp
{
    class Driver
    {
        static Random rnd = new Random();

        static void Main(string[] args)
        {
            int factorme = 30;  //note: trying to factor 21 takes abt 10 minutes per attempt on my PC.

            using (var sim = new QuantumSimulator())
            {
                while (true)
                {
                    var testradix = ChooseRandomCoprime(factorme);

                    Console.WriteLine("Starting Quantum Routine: radix = {0}, modulus = {1}", testradix, factorme);
                    long res = SamplePeriod.Run(sim, testradix, factorme).Result;
                    Console.WriteLine("Result {0}", res);
                    if ((res != 1) && (res != factorme - 1) && (res * res % factorme == 1))
                    {
                        Console.WriteLine("Factors Found: {0} x {1} = {2}", Gcd(res + 1, factorme), factorme / Gcd(res + 1, factorme), factorme);
                        Console.WriteLine("Press any key to continue...");
                        Console.ReadKey();
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