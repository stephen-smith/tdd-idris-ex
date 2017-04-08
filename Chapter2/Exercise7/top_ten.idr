top_ten : Ord a => List a -> List a
top_ten l = take 10 (reverse (sort l))
