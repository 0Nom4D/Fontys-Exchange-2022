package com.example.toysrevive.widgets

import android.net.Uri

import androidx.compose.foundation.ExperimentalFoundationApi
import androidx.compose.foundation.Image
import androidx.compose.foundation.layout.*
import androidx.compose.foundation.pager.HorizontalPager
import androidx.compose.foundation.pager.rememberPagerState
import androidx.compose.foundation.shape.RoundedCornerShape

import androidx.compose.material.*
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.LocationOn

import androidx.compose.runtime.Composable

import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.layout.ContentScale
import androidx.compose.ui.platform.LocalConfiguration
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.res.painterResource
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp

import coil.compose.rememberAsyncImagePainter
import coil.request.ImageRequest

import com.example.toysrevive.R
import com.example.toysrevive.models.ObsolescenceState
import com.example.toysrevive.models.ToyKind
import com.example.toysrevive.models.obsolescenceCorres
import com.example.toysrevive.models.toyKindCorres
import com.example.toysrevive.ui.theme.getPoppins
import com.example.toysrevive.utils.GlobalSettings

@OptIn(ExperimentalFoundationApi::class)
@Composable
fun ToyDescriptionModal() {
    val currentToy = GlobalSettings.currentDetailedToy

    val pagerState = rememberPagerState(
        initialPage = 0
    )

    Box(
        contentAlignment = Alignment.TopCenter,
        modifier = Modifier
            .fillMaxWidth()
            .height(LocalConfiguration.current.screenHeightDp.dp * .9f)
    ) {
        Column(
            horizontalAlignment = Alignment.CenterHorizontally,
            verticalArrangement = Arrangement.Top,
            modifier = Modifier.padding(vertical = 20.dp).fillMaxWidth()
        ) {
            if (currentToy.value != null) {
                currentToy.value?.pictures?.let {
                    Card(
                        elevation = 4.dp, modifier = Modifier
                            .fillMaxHeight(.45f)
                            .fillMaxWidth()
                    ) {
                        HorizontalPager(
                            pageCount = it.size,
                            state = pagerState,
                            verticalAlignment = Alignment.Top,
                            modifier = Modifier.fillMaxSize()
                        ) { idx ->
                            Image(
                                painter = when (currentToy.value!!.isCreated) {
                                    false -> painterResource(id = currentToy.value!!.pictures[idx] as Int)
                                    true -> rememberAsyncImagePainter(
                                        ImageRequest
                                            .Builder(LocalContext.current)
                                            .data(data = currentToy.value!!.pictures[idx] as Uri)
                                            .build()
                                    )
                                    else -> painterResource(id = R.drawable.startreck)
                                },
                                contentDescription = null,
                                contentScale = ContentScale.Fit,
                                modifier = Modifier.fillMaxSize()
                            )
                        }
                    }
                }
                Spacer(modifier = Modifier.height(10.dp))
                Row(horizontalArrangement = Arrangement.Start, verticalAlignment = Alignment.CenterVertically, modifier = Modifier.padding(horizontal = 20.dp).fillMaxWidth()) {
                    Text(
                        text = currentToy.value!!.name,
                        fontFamily = getPoppins(),
                        fontWeight = FontWeight.Bold,
                        fontSize = 25.sp,
                        modifier = Modifier.weight(1f)
                    )
                    Spacer(modifier = Modifier.width(25.dp))
                    Card(
                        shape = RoundedCornerShape(20.dp),
                        elevation = 4.dp,
                        backgroundColor = MaterialTheme.colors.surface,
                        modifier = Modifier.padding(vertical = 10.dp)
                    ) {
                        Text(
                            text = toyKindCorres[enumValues<ToyKind>().indexOf(currentToy.value!!.toyKind)],
                            fontFamily = getPoppins(),
                            fontWeight = FontWeight.Normal,
                            fontSize = 15.sp,
                            modifier = Modifier.padding(horizontal = 10.dp)
                        )
                    }
                }
                Row(horizontalArrangement = Arrangement.Start, verticalAlignment = Alignment.CenterVertically, modifier = Modifier.padding(horizontal = 20.dp).fillMaxWidth()) {
                    Icon(
                        Icons.Default.LocationOn,
                        contentDescription = null,
                        tint = MaterialTheme.colors.onSurface
                    )
                    Text(
                        text = "At ${currentToy.value!!.givingUser.zipCode}",
                        fontFamily = getPoppins(),
                        fontWeight = FontWeight.Bold,
                        fontSize = 15.sp
                    )
                }
                Text(
                    text = obsolescenceCorres[enumValues<ObsolescenceState>().indexOf(currentToy.value!!.obsolescenceState)],
                    fontFamily = getPoppins(),
                    fontWeight = FontWeight.Normal,
                    fontSize = 15.sp,
                    modifier = Modifier.padding(horizontal = 20.dp).align(Alignment.Start)
                )
                Divider(modifier = Modifier.fillMaxWidth().padding(15.dp))
                Text(
                    text = currentToy.value!!.description,
                    fontFamily = getPoppins(),
                    fontWeight = FontWeight.Normal,
                    fontSize = 15.sp,
                    modifier = Modifier.padding(horizontal = 20.dp).align(Alignment.Start)
                )
            }
        }
    }
}