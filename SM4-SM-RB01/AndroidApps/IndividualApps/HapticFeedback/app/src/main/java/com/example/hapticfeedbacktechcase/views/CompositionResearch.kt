package com.example.hapticfeedbacktechcase.views

import android.os.Build
import android.os.VibrationEffect
import android.os.Vibrator
import android.view.HapticFeedbackConstants
import androidx.annotation.RequiresApi

import androidx.compose.foundation.layout.*
import androidx.compose.foundation.lazy.LazyColumn
import androidx.compose.material.Button

import androidx.compose.material.Text

import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember

import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.input.nestedscroll.NestedScrollConnection
import androidx.compose.ui.input.nestedscroll.nestedScroll
import androidx.compose.ui.platform.LocalView
import androidx.compose.ui.text.font.FontStyle
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.text.style.TextAlign
import androidx.compose.ui.unit.Velocity
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp

import com.example.hapticfeedbacktechcase.ui.theme.getPoppins

@OptIn(ExperimentalLayoutApi::class)
@RequiresApi(Build.VERSION_CODES.S)
@Composable
fun CompositionResearch(vibrator: Vibrator, modifier: Modifier = Modifier) {
    val currentView = LocalView.current

    val nestedScrollConnection = remember {
        object : NestedScrollConnection {
            override suspend fun onPreFling(available: Velocity): Velocity {
                currentView.performHapticFeedback(
                    HapticFeedbackConstants.GESTURE_START
                )
                return super.onPreFling(available)
            }

            override suspend fun onPostFling(consumed: Velocity, available: Velocity): Velocity {
                currentView.performHapticFeedback(
                    HapticFeedbackConstants.GESTURE_END
                )
                return super.onPostFling(consumed, available)
            }
        }
    }

    val btnNames = listOf(
        "CLICK", "THUD (Rqs Android S)", "SPIN (Rqs Android S)", "QUICK RISE",
        "SLOW RISE", "QUICK FALL", "TICK"
    )

    val compositionCallbacks = listOf(
        {
            vibrator.vibrate(
                VibrationEffect
                    .startComposition()
                    .addPrimitive(
                        VibrationEffect.Composition.PRIMITIVE_CLICK
                    ).compose()
            )
        },
        {
            vibrator.vibrate(
                VibrationEffect
                    .startComposition()
                    .addPrimitive(
                        VibrationEffect.Composition.PRIMITIVE_THUD
                    ).compose()
            )
        },
        {
            vibrator.vibrate(
                VibrationEffect
                    .startComposition()
                    .addPrimitive(
                        VibrationEffect.Composition.PRIMITIVE_SPIN
                    ).compose()
            )
        },
        {
            vibrator.vibrate(
                VibrationEffect
                    .startComposition()
                    .addPrimitive(
                        VibrationEffect.Composition.PRIMITIVE_QUICK_RISE
                    ).compose()
            )
        },
        {
            vibrator.vibrate(
                VibrationEffect
                    .startComposition()
                    .addPrimitive(
                        VibrationEffect.Composition.PRIMITIVE_SLOW_RISE
                    ).compose()
            )
        },
        {
            vibrator.vibrate(
                VibrationEffect
                    .startComposition()
                    .addPrimitive(
                        VibrationEffect.Composition.PRIMITIVE_QUICK_FALL
                    ).compose()
            )
        },
        {
            vibrator.vibrate(
                VibrationEffect
                    .startComposition()
                    .addPrimitive(
                        VibrationEffect.Composition.PRIMITIVE_TICK
                    ).compose()
            )
        }
    )

    LazyColumn(
        verticalArrangement = Arrangement.Top,
        horizontalAlignment = Alignment.Start,
        modifier = modifier
            .padding(horizontal = 10.dp)
            .nestedScroll(nestedScrollConnection)
    ) {
        item {
            Text(
                "Compositions Research",
                fontFamily = getPoppins(),
                fontSize = 25.sp,
                fontWeight = FontWeight.Bold,
            )
            Text(
                "You will find some composable to test haptic feedback, using compositions, and explanations on how I worked on them. " +
                        "Compositions are a set of predefined hardware vibrations, different from the constants from the previous screen.",
                fontFamily = getPoppins(),
                fontSize = 10.sp,
                fontWeight = FontWeight.Medium,
                fontStyle = FontStyle.Italic
            )
            Spacer(modifier = Modifier.height(15.dp))
            if (vibrator.areAllPrimitivesSupported(VibrationEffect.Composition.PRIMITIVE_CLICK)) {
                FlowRow(
                    maxItemsInEachRow = 2,
                    horizontalArrangement = Arrangement.SpaceAround,
                    verticalAlignment = Alignment.CenterVertically,
                    modifier = Modifier.fillMaxWidth()
                ) {
                    repeat(btnNames.size) { idx ->
                        Button(
                            onClick = compositionCallbacks[idx],
                            modifier = Modifier.width(150.dp).height(70.dp).padding(5.dp)
                        ) {
                            Text(btnNames[idx], textAlign = TextAlign.Center)
                        }
                    }
                }
            } else {
                Text(
                    "Unfortunately, your phone doesn't support compositions primitives.",
                    fontFamily = getPoppins(),
                    fontSize = 15.sp,
                    fontWeight = FontWeight.Bold
                )
            }
        }
    }
}