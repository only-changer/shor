namespace Quantum.test
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Set (desired: Result, q1: Qubit) : ()
    {
        body
        {
            let current = M(q1);

            if (desired != current)
            {
                X(q1);
            } 
        }
    }
	operation Sum (a1 : Qubit , a2 : Qubit , a3 : Qubit) : ()
	{
		body
		{
			CNOT(a2 , a3);
			CNOT(a1 , a3);
		}
	}
	operation Carry(a1 : Qubit , a2 : Qubit , a3 : Qubit , a4 : Qubit) : ()
	{
		body
		{
			CCNOT(a2 , a3 , a4);
			CNOT(a2 , a3);
			CCNOT(a1 , a3 , a4);
		}
	}
	operation inCarry(a1 : Qubit , a2 : Qubit , a3 : Qubit , a4 : Qubit) : ()
	{
		body
		{
			CCNOT(a1 , a3 , a4);	
			CNOT(a2 , a3);
			CCNOT(a2 , a3 , a4);
		}
	}
	operation Adder(a : Qubit[] , b : Qubit[] , c : Qubit[] , d : Qubit) :()
	{
		body
		{
			for (i in 0..3)
			{
				Carry(c[i] , a[i] , b[i] , c[i + 1]);
			}
			Carry(c[4] , a[4] , b[4] , d);
			CNOT(a[4] , b[4]);
			Sum(c[4] , a[4] , b[4]);
			for (i in 0..3)
			{
				inCarry(c[3 - i] , a[3 - i] , b[3 - i] , c[4 - i]);
				Sum(c[3 - i] , a[3 - i] , b[3 - i]);
			}
		}
	}
	operation inAdder(a : Qubit[] , b : Qubit[] , c : Qubit[] , d : Qubit) :()
	{
		body
		{
			for (i in 0..3)
			{
				Sum(c[i] , a[i] , b[i]);
				Carry(c[i] , a[i] , b[i] , c[i + 1]);
			}
			Sum(c[4] , a[4] , b[4]);	
			CNOT(a[4] , b[4]);
			inCarry(c[4] , a[4] , b[4] , d);
			for (i in 0..3)
			{
				inCarry(c[3 - i] , a[3 - i] , b[3 - i] , c[4 - i]);
			}
		}
	}
	operation Add_Mod (a : Qubit[] , b : Qubit[] , n : Qubit[]) : ()
	{
		body
		{
			using (c = Qubit[5])
			{
				for (i in 0..4)
				{
					Set(Zero, c[i]);
				}	
				using (d = Qubit[1])
				{
					Set(Zero , d[0]);
					using (v = Qubit[1])
					{
						Set(Zero , v[0]);
						using (o = Qubit[1])
						{
							Set(One , o[0]);
							Adder(a , b , c , d[0]);
							inAdder(n , b , c , d[0]);
							CNOT(o[0] , d[0]);
							CNOT(d[0] , v[0]);
							CNOT(o[0] , d[0]);
							for (i in 0..4)
							{	
								CNOT(v[0] , n[i]);
							}
							Adder(n , b , c , d[0]);
							for (i in 0..4)
							{
								CNOT(v[0] , n[i]);
							}
							inAdder(a , b , c , d[0]);
							CNOT(d[0] , v[0]);
							Adder(a , b , c , d[0]);
							ResetAll(o);
						}
						ResetAll(v);
					}
					ResetAll(d);
				}
				ResetAll(c);
			}
		}
	}
	operation test() : (Result)
	{
		body
		{
			mutable s = Zero;
			using (a = Qubit[5])
			{
				for (i in 0..4)
				{
					Set(Zero, a[i]);
				}	
				using (b = Qubit[5])
				{
					for (i in 0..4)
					{
						Set(Zero, b[i]);
					}	
					Set(One , b[0]);
					using (n = Qubit[5])
					{
						for (i in 0..4)
						{
							Set(Zero, n[i]);
						}	
						Set(One , n[1]);
						Add_Mod(a , b , n);
						set s = M(b[0]);
						ResetAll(n);
					}
					ResetAll(b);
				}
				ResetAll(a);
			}	
			return s;
		}
	}
	operation BellTest() : (Result, Result)
	{
		body
		{
			// 用于保存量子位状态的可变局部变量
			mutable s1 = Zero;
			mutable s2 = Zero;

			// 分配两个量子位
			using (qubits = Qubit[2])
			{
				// 将第一个量子位执行阿达马门实现状态叠加
				H(qubits[0]);
	
				// 通过可控非门将两个量子进行纠缠
				CNOT(qubits[0], qubits[1]);

				// 测量两个量子位的状态
				set s1 = M(qubits[0]);
				set s2 = M(qubits[1]);

				// 释放量子位前需要将其重置0状态
				Set(Zero, qubits[0]);
				Set(Zero, qubits[1]);
			}

			// 返回两个量子位的状态
			return (s1, s2);
		}
    }
}
