package com.example.toysrevive.views

import android.net.Uri

import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.painterResource
import androidx.compose.ui.unit.dp

import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.padding

import androidx.compose.material.*
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.Lock

import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope

import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.text.style.TextAlign
import androidx.compose.ui.unit.sp

import coil.compose.rememberAsyncImagePainter
import coil.request.ImageRequest

import com.alexstyl.swipeablecard.ExperimentalSwipeableCardApi
import com.alexstyl.swipeablecard.rememberSwipeableCardState
import com.alexstyl.swipeablecard.Direction
import com.alexstyl.swipeablecard.swipableCard

import com.example.toysrevive.R
import com.example.toysrevive.ui.theme.getPoppins
import com.example.toysrevive.widgets.SwipedImageCard
import com.example.toysrevive.utils.GlobalSettings

//vibration
import android.os.Vibrator
import android.content.Context
import kotlinx.coroutines.launch

//sound effects
import android.media.MediaPlayer
import android.os.Build
import android.os.VibrationEffect
import androidx.annotation.RequiresApi


@RequiresApi(Build.VERSION_CODES.Q)
@OptIn(ExperimentalSwipeableCardApi::class, ExperimentalMaterialApi::class)
@Composable
fun SwipingScreen(bottomSheetState: ModalBottomSheetState, modifier: Modifier = Modifier) {
    val coroutineScope = rememberCoroutineScope()
    val vibrator = LocalContext.current.getSystemService(Context.VIBRATOR_SERVICE) as Vibrator
    val context = LocalContext.current
    val liked = remember { MediaPlayer.create(context, R.raw.liked) }

    Column(horizontalAlignment = Alignment.CenterHorizontally, verticalArrangement = Arrangement.Center, modifier = modifier.fillMaxSize()) {
        Box(
            contentAlignment = Alignment.Center,
            modifier = Modifier
                .fillMaxSize()
                .padding(15.dp)
        ) {
            if (GlobalSettings.availableToys.isEmpty()) {
                Column(horizontalAlignment = Alignment.CenterHorizontally, verticalArrangement = Arrangement.Center, modifier = Modifier.fillMaxSize()) {
                    Icon(
                        painterResource(id = R.drawable.baseline_no_likes_24),
                        contentDescription = null,
                        modifier = Modifier.fillMaxSize(.6f)
                    )
                    Text(
                        "There is no toy left to see there. Check later to see if new people wants to make this world better!",
                        textAlign = TextAlign.Center,
                        fontFamily = getPoppins(),
                        fontWeight = FontWeight.Medium,
                        fontSize = 12.sp,
                    )
                }
            } else if (GlobalSettings.doesRespectCardLimitation()) {
                val states = GlobalSettings.availableToys.reversed().map {data -> data to rememberSwipeableCardState() }
                states.forEach { (toy, state) ->
                    if (state.swipedDirection == null) {
                        SwipedImageCard(
                            painter = when (toy.isCreated) {
                                false -> painterResource(id = toy.pictures[0] as Int)
                                true -> rememberAsyncImagePainter(
                                    ImageRequest
                                        .Builder(LocalContext.current)
                                        .data(data = toy.pictures[0] as Uri)
                                        .build()
                                )
                            },
                            contentDescription = toy.description,
                            imageTitle = toy.name,
                            state = state,
                            modifier = Modifier.swipableCard(
                                state = state,
                                blockedDirections = listOf(Direction.Left, Direction.Right),
                                onSwiped = { direction ->
                                    when (direction) {
                                        Direction.Up -> {
                                            if (GlobalSettings.isCardLimitEnabled)
                                                GlobalSettings.currentSwipedCards += 1
                                            GlobalSettings.availableToys.remove(toy)
                                            vibrator.vibrate(VibrationEffect.createPredefined(VibrationEffect.EFFECT_CLICK))
                                        }
                                        Direction.Down -> {
                                            if (GlobalSettings.isCardLimitEnabled)
                                                GlobalSettings.currentSwipedCards += 1
                                            GlobalSettings.likeToy(toy)
                                            vibrator.vibrate(VibrationEffect.createPredefined(VibrationEffect.EFFECT_CLICK))
                                            liked.start()

                                        }
                                        else -> {}
                                    }
                                },
                            ),
                            onDetailButtonClicked = {
                                GlobalSettings.isToyDescription.value = true
                                GlobalSettings.currentDetailedToy.value = toy
                                coroutineScope.launch {
                                    GlobalSettings.showCallbackModal(
                                        bottomSheetState
                                    )
                                }
                            },
                            onLikedCard = {
                                if (GlobalSettings.isCardLimitEnabled)
                                    GlobalSettings.currentSwipedCards += 1
                                GlobalSettings.likeToy(toy)
                            },
                            onDislikeCard = {
                                if (GlobalSettings.isCardLimitEnabled)
                                    GlobalSettings.currentSwipedCards += 1
                                GlobalSettings.availableToys.remove(toy)
                            }
                        )
                    }
                }
            } else {
                Column(horizontalAlignment = Alignment.CenterHorizontally, verticalArrangement = Arrangement.Center, modifier = Modifier.fillMaxSize()) {
                    Icon(
                        Icons.Default.Lock,
                        contentDescription = null,
                        modifier = Modifier.fillMaxSize(.6f)
                    )
                    Text(
                        "You can't swipe cards anymore for now. Ask your parents to unlock limitations or wait until tomorrow!",
                        textAlign = TextAlign.Center,
                        fontFamily = getPoppins(),
                        fontWeight = FontWeight.Medium,
                        fontSize = 12.sp,
                    )
                }
            }
        }
    }
}