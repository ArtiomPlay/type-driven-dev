module Prat11
import Data.Vect

%default total

namespace MatterTask
    data Matter = Solid | Liquid | Gas

    data MatterCmd : Type -> Matter -> Matter -> Type where
        Melt : MatterCmd () Solid Liquid
        Boil : MatterCmd () Liquid Gas
        Condence : MatterCmd () Gas Liquid
        Freeze : MatterCmd () Liquid Solid
        (>>=) :
            MatterCmd a m1 m2 ->
            (a -> MatterCmd b m2 m3) ->
            MatterCmd b m1 m3
        (>>) :
            MatterCmd a m1 m2 ->
            (MatterCmd b m2 m3) ->
            MatterCmd b m1 m3

    matterProg1 : MatterCmd () Solid Gas 
    matterProg1 =
        do  Melt
            Boil

    matterProg2 : MatterCmd () Gas Solid 
    matterProg2 =
        do  Condence
            Freeze
    failing
        matterProg3 : MatterCmd () Solid Gas 
        matterProg3 =
            do  Melt
                Melt

namespace StackTask
    data PushRes = Success | Failed

    data StackCmd :
        (return : Type) ->
        (preState : Nat) ->
        (postState : Nat) ->
        Type where
        Push : Int -> StackCmd () n (S n)
        Pop : StackCmd Int (S n) n
        Top : StackCmd Int (S n) (S n)
        Pure : a -> StackCmd a 0 0
        (>>=) :
            StackCmd a m1 m2 ->
            (a -> StackCmd b m2 m3) ->
            StackCmd b m1 m3
        (>>) :
            StackCmd a m1 m2 ->
            (StackCmd b m2 m3) ->
            StackCmd b m1 m3

    add : StackCmd Int (S (S n)) (S n)
    add =
        do  x <- Pop
            y <- Pop
            Push (x + y)
            Top

    mul : StackCmd () (S (S n)) (S n)
    mul =
        do  x <- Pop
            y <- Pop
            Push (x * y)

    func : StackCmd () (S (S (S n))) (S n)
    func =
        do  x <- Pop
            y <- Pop
            z <- Pop
            Push (x * (y + z))

    stackProg : StackCmd () 0 2
    stackProg =
        do  Pure ()
            Push 1
            Push 2
            a <- Top
            b <- Pop
            Push 3

namespace StackTaskCanFail
    data PushRes = Success | Failed

    data StackCmd :
        (res : Type) ->
        (preState : Nat) ->
        (res -> Nat) ->
        Type where
        Push : Int -> StackCmd PushRes n
            (\res =>
                case res of
                    Success => (S n)
                    Failed => n
            )
        Pop : StackCmd Int (S n) (const n)
        Top : StackCmd Int (S n) (const (S n))
        Fail : StackCmd () (S n) (const (S n))
        Pure : a -> StackCmd a 0 (const 0)
        (>>=) :
            StackCmd a m1 mf2 ->
            ((res : a) -> StackCmd b (mf2 res) m3) ->
            StackCmd b m1 m3
        (>>) :
            StackCmd a m1 (\_ => m2) ->
            (StackCmd b m2 m3) ->
            StackCmd b m1 m3

    -- add : StackCmd Int (S (S n)) (const (S n))
    -- add =
    --     do  x <- Pop
    --         y <- Pop
    --         Success <- Push (x + y) | Failed => Fail
    --         Top

    -- mul : StackCmd Int (S (S n)) (const (S n))
    -- mul =
    --     do  x <- Pop
    --         y <- Pop
    --         Success <- Push (x * y) | Failed => ?mul_push_failed
    --         Top

    -- func : StackCmd Int (S (S (S n))) (const (S n))
    -- func =
    --     do  x <- Pop
    --         y <- Pop
    --         z <- Pop
    --         Success <- Push (x * (y + z)) | Failed => ?func_push_failed
    --         Top

    -- stackProg : StackCmd Int 0 (const 2)
    -- stackProg =
    --     do  Pure ()
    --         Success <- Push 1 | Failed => ?prog_push1_failed
    --         Success <- Push 1 | Failed => ?prog_push2_failed
    --         a <- Top
    --         b <- Pop
    --         Success <- Push 3 | Failed => ?prog_push3_failed
    --         Top
