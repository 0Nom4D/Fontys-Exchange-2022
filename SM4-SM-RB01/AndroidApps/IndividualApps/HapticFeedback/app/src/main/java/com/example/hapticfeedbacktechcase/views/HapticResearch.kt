package com.example.hapticfeedbacktechcase.views

import android.os.Build
import android.view.HapticFeedbackConstants
import androidx.annotation.RequiresApi
import androidx.compose.foundation.layout.*
import androidx.compose.foundation.lazy.LazyColumn
import androidx.compose.material.Divider
import androidx.compose.material.ScaffoldState
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
import androidx.compose.ui.unit.Velocity
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp

import com.example.hapticfeedbacktechcase.composables.HapticFeedbackTextField
import com.example.hapticfeedbacktechcase.composables.LongClickButton
import com.example.hapticfeedbacktechcase.composables.SimpleClickButton

import com.example.hapticfeedbacktechcase.ui.theme.getPoppins

@RequiresApi(Build.VERSION_CODES.R)
@Composable
fun HapticResearch(scaffoldState: ScaffoldState, modifier: Modifier = Modifier) {
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

    LazyColumn(
        verticalArrangement = Arrangement.Top,
        horizontalAlignment = Alignment.Start,
        modifier = modifier
            .padding(horizontal = 10.dp)
            .nestedScroll(nestedScrollConnection)
    ) {
        item {
            Text(
                "Haptic Research",
                fontFamily = getPoppins(),
                fontSize = 25.sp,
                fontWeight = FontWeight.Bold,
            )
            Text(
                "You will find some composable to test haptic feedback and explanations on how I worked on them.",
                fontFamily = getPoppins(),
                fontSize = 10.sp,
                fontWeight = FontWeight.Medium,
                fontStyle = FontStyle.Italic
            )
            Spacer(modifier = Modifier.height(15.dp))
            SimpleClickButton()
            Divider(modifier = Modifier.fillMaxWidth().padding(vertical = 10.dp))
            LongClickButton()
            Divider(modifier = Modifier.fillMaxWidth().padding(vertical = 10.dp))
            HapticFeedbackTextField()
            Divider(modifier = Modifier.fillMaxWidth().padding(vertical = 10.dp))
        }
    }
}