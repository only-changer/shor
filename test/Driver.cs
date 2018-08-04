using Microsoft.Quantum.Simulation.Core;
using Microsoft.Quantum.Simulation.Simulators;
using System;

namespace Quantum.test
{
    class Driver
    {
        static void Main(string[] args)
        {
            using (var sim = new QuantumSimulator())
            {
                var s1 = test.Run(sim).Result;
                Console.WriteLine(s1);
            }

            Console.WriteLine("按任意键继续...");
            Console.ReadKey();
        }
    }
}