namespace Quantum.ShorQsharp
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	//open Microsoft.Quantum.Canon.ModularMultiplyByConstantLE;
    open Microsoft.Quantum.Extensions.Math;
	//using System;
	function Expmod(radix : Int , cleanedPeriod : Int ,modulus : Int):(Int)
	{
            mutable x = radix;
            mutable ans = 1;
            mutable k = cleanedPeriod;

            for(i in 0..5)
			{
                if(k % 2 == 1)
				{
                    set ans = ans * x % modulus;
                }
                set x = x * x % modulus;
                set k = k / 2;
            }
            return ans;
    }
	operation SamplePeriod (radix: Int, modulus: Int ) : (Int)
    {
        body
        {
			mutable measuredPeriod = 0;
			let registersize = 2*BitSize(modulus)+1;

			using ( targetState = Qubit[BitSize(modulus)] )
			{
				using ( controlRegister = Qubit[registersize] )
				{
					IntegerIncrementLE( 1 , LittleEndian(targetState) );
					QuantumPhaseEstimation( DiscreteOracle(PowerOracle(radix,modulus,_,_)) , LittleEndian(targetState) , BigEndian(controlRegister) );
					set measuredPeriod = MeasureIntegerBE( BigEndian(controlRegister) );
					ResetAll(targetState);
				}
			}

		    let cleanedPeriod = AbsI(Snd( ContinuedFractionConvergent( Fraction(measuredPeriod, 2^(registersize)) , modulus ) )) ;			

			return Expmod(radix, cleanedPeriod/2 , modulus ); 
		}
    }

	operation PowerOracle (radix: Int, modulus: Int, power: Int, target: Qubit[]) : ()
	{
		body
		{
			ModularMultiplyByConstantLE( Expmod(radix,power,modulus), modulus, LittleEndian(target));
		}
		adjoint auto
		controlled auto
		adjoint controlled auto
	}
}