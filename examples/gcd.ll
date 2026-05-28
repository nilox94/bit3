; ModuleID = 'gcd.ll'
source_filename = "gcd.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @gcd(i32 noundef %a, i32 noundef %b) #0 {
entry:
  %tobool = icmp ne i32 %b, 0
  br i1 %tobool, label %if.then, label %entry.return_crit_edge

entry.return_crit_edge:                           ; preds = %entry
  br label %return

if.then:                                          ; preds = %entry
  %rem = srem i32 %a, %b
  %call = call i32 @gcd(i32 noundef %b, i32 noundef %rem)
  br label %return

return:                                           ; preds = %entry.return_crit_edge, %if.then
  %retval.0 = phi i32 [ %call, %if.then ], [ %a, %entry.return_crit_edge ]
  ret i32 %retval.0
}

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{!"Apple clang version 17.0.0 (clang-1700.0.13.5)"}
