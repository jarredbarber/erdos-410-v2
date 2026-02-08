import math

def sigma(n):
    if n == 1: return 1
    sum_div = 1
    d = 2
    temp = n
    while d * d <= temp:
        if temp % d == 0:
            p_sum = 1
            cur_p = 1
            while temp % d == 0:
                cur_p *= d
                p_sum += cur_p
                temp //= d
            sum_div *= p_sum
        d += 1
    if temp > 1:
        sum_div *= (1 + temp)
    return sum_div

def analyze_sequence(start_n, steps):
    a = start_n
    r_values = []
    odd_indices = []
    mersenne_indices = [] # a_k is Mersenne prime (or just 2^n-1)
    
    # Check if number is 2^n - 1
    def is_mersenne_form(x):
        return (x + 1) & x == 0

    # Limit steps based on magnitude.
    # Trial division up to 10^7 is fast enough (takes ~1s).
    # So if a > 10^14, it might be slow.
    limit = 10**14

    for k in range(steps):
        if a > limit:
            print(f"Stopping at step {k} because a={a} is too large (>10^14)")
            break
            
        r = sigma(a) / a
        r_values.append(r)
        
        if a % 2 != 0:
            odd_indices.append(k)
            if is_mersenne_form(a):
                mersenne_indices.append(k)
        
        # Optimization: if a becomes too large, we might stop or handle it
        # But for 100-200 steps it might explode. 
        # Python handles large integers automatically.
        
        next_a = sigma(a)
        if next_a == a: # Perfect number (unlikely for large)
            break
        a = next_a
        
        # Safety break if too slow (though 100 steps should be fine)
        if k % 100 == 0:
            print(f"Step {k}: a_k has {len(str(a))} digits")

    return r_values, odd_indices, mersenne_indices

def run_experiment():
    starts = [2, 3, 4, 5, 6, 7, 10, 12, 100, 101, 127]
    results = {}
    
    for n in starts:
        print(f"Analyzing n={n}...")
        try:
            r, odds, mers = analyze_sequence(n, 200)
            
            # Calculate stats
            avg_r = sum(r) / len(r)
            odd_density = len(odds) / len(r)
            low_r_count = sum(1 for x in r if x < 1.5)
            low_r_density = low_r_count / len(r)
            
            # Geometric mean of growth factors?
            # a_k^{1/k} -> exp(average log R)
            log_sum = sum(math.log(x) for x in r)
            avg_log_r = log_sum / len(r)
            growth_base = math.exp(avg_log_r)

            results[n] = {
                "odd_density": odd_density,
                "low_r_density": low_r_density, # Should be same as odd_density mostly
                "avg_r": avg_r,
                "avg_log_r": avg_log_r,
                "growth_base": growth_base,
                "final_r": r[-1]
            }
        except Exception as e:
            print(f"Error with n={n}: {e}")

    # Print summary
    print("\n--- RESULTS ---")
    print(f"{'n':<5} {'Odd%':<10} {'<1.5%':<10} {'Avg R':<10} {'Avg ln R':<10} {'Growth':<10}")
    for n, data in results.items():
        print(f"{n:<5} {data['odd_density']:.3f}      {data['low_r_density']:.3f}      {data['avg_r']:.3f}      {data['avg_log_r']:.3f}      {data['growth_base']:.3f}")

if __name__ == "__main__":
    run_experiment()
