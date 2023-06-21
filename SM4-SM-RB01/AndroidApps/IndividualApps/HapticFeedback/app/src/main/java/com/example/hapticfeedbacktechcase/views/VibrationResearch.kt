package com.example.hapticfeedbacktechcase.views

import android.os.Build
import android.os.VibrationEffect
import android.os.Vibrator
import android.view.HapticFeedbackConstants
import androidx.annotation.RequiresApi

import androidx.compose.foundation.layout.*
import androidx.compose.foundation.lazy.LazyColumn
import androidx.compose.foundation.selection.selectable
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.foundation.text.KeyboardActions
import androidx.compose.foundation.text.KeyboardOptions
import androidx.compose.material.*

import androidx.compose.runtime.Composable
import androidx.compose.runtime.*

import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.input.nestedscroll.NestedScrollConnection
import androidx.compose.ui.input.nestedscroll.nestedScroll
import androidx.compose.ui.platform.LocalView
import androidx.compose.ui.text.font.FontStyle
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.text.input.KeyboardType
import androidx.compose.ui.text.style.TextAlign
import androidx.compose.ui.unit.Velocity
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp

import com.example.hapticfeedbacktechcase.ui.theme.getPoppins

@OptIn(ExperimentalLayoutApi::class)
@RequiresApi(Build.VERSION_CODES.S)
@Composable
fun VibrationResearch(vibrator: Vibrator, modifier: Modifier = Modifier) {
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

    val btnNames = listOf("TICK", "CLICK", "EFFECT HEAVY CLICK", "EFFECT DOUBLE CLICK")
    val compositionCallbacks = listOf(
        { vibrator.vibrate(VibrationEffect.createPredefined(VibrationEffect.EFFECT_TICK)) },
        { vibrator.vibrate(VibrationEffect.createPredefined(VibrationEffect.EFFECT_CLICK)) },
        { vibrator.vibrate(VibrationEffect.createPredefined(VibrationEffect.EFFECT_HEAVY_CLICK)) },
        { vibrator.vibrate(VibrationEffect.createPredefined(VibrationEffect.EFFECT_DOUBLE_CLICK)) }
    )

    val vibrationOptions = listOf("Waveform Vibration", "Oneshot Vibration")
    val (selectedOption, onOptionSelected) = remember { mutableStateOf(vibrationOptions[0] ) }

    var firstParam by remember { mutableStateOf("") }
    var firstIntParam by remember { mutableStateOf(0) }

    var secondParam by remember { mutableStateOf("") }
    var secondIntParam by remember { mutableStateOf(1) }

    var repeatParam by remember { mutableStateOf(-1) }

    LazyColumn(
        verticalArrangement = Arrangement.Top,
        horizontalAlignment = Alignment.Start,
        modifier = modifier
            .padding(horizontal = 10.dp)
            .nestedScroll(nestedScrollConnection)
    ) {
        item {
            Text(
                "Vibration Research",
                fontFamily = getPoppins(),
                fontSize = 25.sp,
                fontWeight = FontWeight.Bold,
            )
            Text(
                "You will find some composable to test haptic feedback, using Waveform and one shot vibration, and explanations on how I worked on them.",
                fontFamily = getPoppins(),
                fontSize = 10.sp,
                fontWeight = FontWeight.Medium,
                fontStyle = FontStyle.Italic
            )
            Divider(modifier = Modifier.fillMaxWidth().padding(vertical = 10.dp))
            Text(
                "Here are some predefined vibration with different amplitudes.",
                fontFamily = getPoppins(),
                fontSize = 12.sp,
                fontWeight = FontWeight.Medium,
                fontStyle = FontStyle.Italic
            )
            FlowRow(
                maxItemsInEachRow = 2,
                horizontalArrangement = Arrangement.SpaceAround,
                verticalAlignment = Alignment.CenterVertically,
                modifier = Modifier.fillMaxWidth()
            ) {
                repeat(btnNames.size) { idx ->
                    Button(
                        onClick = compositionCallbacks[idx],
                        modifier = Modifier
                            .width(178.dp)
                            .height(70.dp)
                            .padding(5.dp)
                    ) {
                        Text(btnNames[idx], textAlign = TextAlign.Center)
                    }
                }
            }
            Divider(modifier = Modifier.fillMaxWidth().padding(vertical = 10.dp))
            Text(
                "Even if the documentation doesn't recommend to use Vibrator.createOneShot and Vibrator.createWaveform. I still wanted to see what it could offer. " +
                        "So I implemented those methods.",
                fontFamily = getPoppins(),
                fontSize = 12.sp,
                fontWeight = FontWeight.Medium,
                fontStyle = FontStyle.Italic
            )
            Row(horizontalArrangement = Arrangement.SpaceEvenly, verticalAlignment = Alignment.CenterVertically, modifier = Modifier.fillMaxWidth()) {
                vibrationOptions.forEach { option ->
                    Row(
                        verticalAlignment = Alignment.CenterVertically,
                        modifier = Modifier
                            .selectable(
                                selected = selectedOption == option,
                                onClick = {
                                    onOptionSelected(option)
                                    currentView.performHapticFeedback(HapticFeedbackConstants.CONTEXT_CLICK)
                                }
                            )
                            .padding(horizontal = 8.dp)
                    ) {
                        RadioButton(
                            selected = selectedOption == option,
                            onClick = { onOptionSelected(option) }
                        )
                        Text(
                            option,
                            fontFamily = getPoppins(),
                            fontSize = 12.sp,
                            fontWeight = FontWeight.Medium,
                            fontStyle = FontStyle.Italic
                        )
                    }
                }
            }
            TextField(
                value = if (selectedOption == vibrationOptions[1]) firstIntParam.toString() else firstParam,
                onValueChange = {
                    if (selectedOption == vibrationOptions[1])
                        firstIntParam = if (it.isEmpty()) 0 else it.toInt()
                    else
                        firstParam = it
                },
                label = {
                    Text(
                        text = if (selectedOption == vibrationOptions[0])
                            "Timings of parts of the vibration"
                        else "Duration of vibration"
                    )
                },
                placeholder = {
                    Text(
                        text = if (selectedOption == vibrationOptions[0])
                            "Timings of sequences separated by commas"
                        else "Duration of vibration"
                    )
                },
                singleLine = true,
                maxLines = 1,
                keyboardOptions = KeyboardOptions(
                    keyboardType = if (selectedOption == vibrationOptions[0]) KeyboardType.Text else KeyboardType.Number
                ),
                colors = TextFieldDefaults.textFieldColors(
                    textColor = MaterialTheme.colors.onSurface,
                    backgroundColor = MaterialTheme.colors.surface
                ),
                shape = RoundedCornerShape(5.dp),
                modifier = Modifier
                    .fillMaxWidth()
                    .padding(5.dp)
            )
            TextField(
                value = if (selectedOption == vibrationOptions[1]) secondIntParam.toString() else secondParam,
                onValueChange = {
                    it.replace("\n", "")
                    if (selectedOption == vibrationOptions[1]) {
                        secondIntParam = if (it.isEmpty()) 1 else if (it.toInt() in (1..255)) {
                            if (it.isEmpty()) 1 else it.toInt()
                        } else if (it.toInt() > 255) {
                            255
                        } else {
                            1
                        }
                    } else {
                        secondParam = it
                    }
                },
                label = {
                    Text(
                        text = if (selectedOption == vibrationOptions[0])
                            "List of amplitudes" else "Amplitude of vibration"
                    )
                },
                placeholder = {
                    Text(
                        text = if (selectedOption == vibrationOptions[0])
                            "List of amplitudes separated by commas"
                        else "Amplitude of vibration"
                    )
                },
                singleLine = true,
                maxLines = 1,
                keyboardOptions = KeyboardOptions(
                    keyboardType = if (selectedOption == vibrationOptions[0]) KeyboardType.Text else KeyboardType.Number
                ),
                colors = TextFieldDefaults.textFieldColors(
                    textColor = MaterialTheme.colors.onSurface,
                    backgroundColor = MaterialTheme.colors.surface
                ),
                shape = RoundedCornerShape(5.dp),
                modifier = Modifier
                    .fillMaxWidth()
                    .padding(5.dp)
            )
            if (selectedOption == vibrationOptions[0]) {
                TextField(
                    value = repeatParam.toString(),
                    onValueChange = {
                        repeatParam = it.toInt()
                    },
                    label = { Text(text = "Repetitions") },
                    placeholder = { Text(text = "Number of repetitions for the vibration") },
                    singleLine = true,
                    maxLines = 1,
                    colors = TextFieldDefaults.textFieldColors(
                        textColor = MaterialTheme.colors.onSurface,
                        backgroundColor = MaterialTheme.colors.surface
                    ),
                    shape = RoundedCornerShape(5.dp),
                    modifier = Modifier
                        .fillMaxWidth()
                        .padding(5.dp)
                )
            }
            Button(
                onClick = {
                    if (selectedOption == vibrationOptions[0]) {
                        vibrator.vibrate(
                            VibrationEffect.createWaveform(
                                firstParam.split(",").map { it.toLong() }.toLongArray(),
                                secondParam.split(",").map { it.toInt() }.toIntArray(),
                                repeatParam
                            )
                        )
                    } else {
                        vibrator.vibrate(
                            VibrationEffect.createOneShot(firstIntParam.toLong(), secondIntParam)
                        )
                    }
                }
            ) { Text("Test Vibration") }
        }
    }
}