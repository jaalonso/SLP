theory Simplificacion4
imports Main
begin

subsection{* Distinción de casos *}

text {* Ejemplos de distinción automática de casos con if *}
lemma "P (if A then s else t)
       = ((A \<longrightarrow> P(s)) \<and> (\<not>A \<longrightarrow> P(t)))"
apply simp
done

lemma "(if A then B else False)
       = (A \<and> B)"
apply simp
done

lemma "(if A then B else C)
       = ((A \<longrightarrow> B) \<and> (\<not>A \<longrightarrow> C))"
apply simp
done

text {* Ejemplos de distinción no automática de casos con case *}

lemma "P (case e of 0 \<Rightarrow> a | Suc n \<Rightarrow> b)
       = ((e = 0 \<longrightarrow> P(a)) \<and> (\<forall> n. e = Suc n \<longrightarrow> P(b)))"
apply (simp split: nat.split)
done

lemma "P (case xs of [] \<Rightarrow> a | (y#ys) \<Rightarrow> b) 
       = ((xs = [] \<longrightarrow> P a ) \<and> ((\<exists>y ys. xs = y # ys) \<longrightarrow> P b))"
apply (simp split: list.split)
done

lemma "1 \<le> (case ns of [] \<Rightarrow> 1 | n#_ \<Rightarrow> Suc n)"
apply (simp split: list.split)
done

lemma "P (case t of (x,y) \<Rightarrow> f x y)
       = (\<forall> x y. t = (x,y) \<longrightarrow> P (f x y))"
apply (simp split: prod.split)
done

text {* Ejemplos de distinción no automática de casos con let *}

lemma "P (let (x,y) = t in f x y)
       = (\<forall> x y. t = (x,y) \<longrightarrow> P (f x y))"
apply (simp split: prod.split)
done

section {* Simplificación en aritmética lineal *}

text {* Ejemplo de simplificación con las reglas de la aritmética
  lineal. *} 
lemma "\<lbrakk> (x::nat) \<le> y+z
       ; z+x < y \<rbrakk> 
       \<Longrightarrow> x < y"
apply simp
done

end
