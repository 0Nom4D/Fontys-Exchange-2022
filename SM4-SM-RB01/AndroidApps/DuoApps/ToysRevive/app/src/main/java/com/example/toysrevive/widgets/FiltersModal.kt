package com.example.toysrevive.widgets

import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.*
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.foundation.text.KeyboardActions

import androidx.compose.material.*
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.outlined.Check

import androidx.compose.runtime.*

import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.platform.LocalConfiguration
import androidx.compose.ui.text.TextStyle
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.text.style.TextAlign
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp
import com.example.toysrevive.models.ObsolescenceState
import com.example.toysrevive.models.ToyKind
import com.example.toysrevive.models.obsolescenceCorres
import com.example.toysrevive.models.toyKindCorres

import com.example.toysrevive.ui.theme.getPoppins
import com.example.toysrevive.utils.GlobalSettings

import kotlin.math.roundToInt

@Composable
fun FiltersModal() {
    var isFingerprintProtected by remember { mutableStateOf(GlobalSettings.isFingerprintProtected) }

    Box(
        contentAlignment = Alignment.TopCenter,
        modifier = Modifier
            .fillMaxWidth()
            .height(LocalConfiguration.current.screenHeightDp.dp * .9f)
    ) {
        Column(
            horizontalAlignment = Alignment.CenterHorizontally,
            verticalArrangement = Arrangement.Center,
            modifier = Modifier.padding(20.dp)
        ) {
            Text("Settings", fontFamily = getPoppins(), fontWeight = FontWeight.Bold, fontSize = 20.sp)
            Divider(modifier = Modifier.fillMaxWidth(.9f).padding(vertical = 10.dp))
            Text("Location", fontFamily = getPoppins(), fontWeight = FontWeight.Bold, fontSize = 20.sp, modifier = Modifier.align(Alignment.Start)
            )
            LocationSettings()
            Spacer(modifier = Modifier.height(25.dp))
            Text("Parental Control", fontFamily = getPoppins(), fontWeight = FontWeight.Bold, fontSize = 20.sp, modifier = Modifier.align(Alignment.Start))
            ParentalControl(
                isFingerprintProtected
            ) {
                isFingerprintProtected = !isFingerprintProtected
                GlobalSettings.isFingerprintProtected = isFingerprintProtected
            }
        }
    }
}

@Composable
fun LocationSettings() {
    var zipCode by remember { mutableStateOf("") }
    var range by remember { mutableStateOf(0f) }

    val zipCodeRegex = Regex("^\\d{4}\\w{2}")

    Card(
        shape = RoundedCornerShape(10.dp),
        elevation = 4.dp,
        backgroundColor = MaterialTheme.colors.surface,
        modifier = Modifier.padding(vertical = 10.dp)
    ) {
        Row(
            horizontalArrangement = Arrangement.SpaceBetween,
            verticalAlignment = Alignment.CenterVertically,
            modifier = Modifier.fillMaxWidth(.9f)
        ) {
            Text(
                "Neighborhood Zipcode",
                fontFamily = getPoppins(),
                fontWeight = FontWeight.Medium,
                fontSize = 12.sp,
                modifier = Modifier.padding(horizontal = 5.dp)
            )
            TextField(
                value = zipCode,
                onValueChange = {
                    if (it.length <= 6)
                        zipCode = it
                },
                textStyle = TextStyle(
                    fontFamily = getPoppins(),
                    fontWeight = FontWeight.Bold,
                    fontSize = 12.sp,
                    textAlign = TextAlign.Center
                ),
                isError = !zipCodeRegex.matches(zipCode),
                placeholder = {
                    Text(
                        text = "5622AV",
                        fontFamily = getPoppins(),
                        fontWeight = FontWeight.Bold,
                        fontSize = 12.sp,
                        textAlign = TextAlign.Center
                    )
                },
                keyboardActions = KeyboardActions.Default,
                maxLines = 1,
                colors = TextFieldDefaults.textFieldColors(
                    textColor = MaterialTheme.colors.onSurface,
                    backgroundColor = MaterialTheme.colors.surface
                ),
                shape = RoundedCornerShape(5.dp),
                modifier = Modifier
                    .height(58.dp)
                    .width(95.dp)
                    .padding(5.dp)
            )
        }
    }
    Card(
        shape = RoundedCornerShape(10.dp),
        elevation = 4.dp,
        backgroundColor = MaterialTheme.colors.surface,
        modifier = Modifier.padding(vertical = 10.dp)
    ) {
        Row(
            horizontalArrangement = Arrangement.SpaceBetween,
            verticalAlignment = Alignment.CenterVertically,
            modifier = Modifier
                .fillMaxWidth(.9f)
                .padding(2.dp)
        ) {
            Text("Range", fontFamily = getPoppins(), fontWeight = FontWeight.Bold, fontSize = 12.sp, modifier = Modifier.padding(horizontal = 5.dp))
            Text(
                if (range < .005f) "Unlimited range" else "${(range * 100).roundToInt()} KM",
                fontFamily = getPoppins(),
                fontWeight = FontWeight.Medium,
                fontSize = 12.sp,
                modifier = Modifier.padding(horizontal = 5.dp)
            )
        }
        Slider(
            range,
            onValueChange = {
                range = it
            },
            colors = SliderDefaults.colors(
                thumbColor = MaterialTheme.colors.secondary,
                activeTrackColor = MaterialTheme.colors.secondary,
                activeTickColor = MaterialTheme.colors.secondary
            ),
            modifier = Modifier
                .fillMaxWidth(.9f)
                .padding(top = 10.dp, bottom = 5.dp, start = 10.dp, end = 10.dp)
        )
    }
}

data class ListItem(val name: String, val isSelected: Boolean)

@OptIn(ExperimentalMaterialApi::class)
@Composable
fun ParentalControl(fingerProtection: Boolean, onActivateFingerProtection: (Boolean) -> Unit) {
    var items by remember {
        mutableStateOf((1 until enumValues<ToyKind>().size).map {
            ListItem(
                name = toyKindCorres[it],
                isSelected = GlobalSettings.filteredToyKind.contains(enumValues<ToyKind>()[it])
            )
        })
    }

    var filterName by remember { mutableStateOf(GlobalSettings.getFilterName()) }
    var filterExpanded by remember { mutableStateOf(false) }
    var limitNumber by remember { mutableStateOf(0f) }

    Card(
        shape = RoundedCornerShape(10.dp),
        elevation = 4.dp,
        backgroundColor = MaterialTheme.colors.surface,
        modifier = Modifier.padding(vertical = 10.dp)
    ) {
        Row(
            horizontalArrangement = Arrangement.SpaceBetween,
            verticalAlignment = Alignment.CenterVertically,
            modifier = Modifier
                .fillMaxWidth(.9f)
                .padding(2.dp)
        ) {
            Text("Card Limit", fontFamily = getPoppins(), fontWeight = FontWeight.Bold, fontSize = 12.sp, modifier = Modifier.padding(horizontal = 5.dp))
            Text(
                if (limitNumber < .05f) "No Limit" else "Limited to ${GlobalSettings.cardNbLimit.value} cards",
                fontFamily = getPoppins(),
                fontWeight = FontWeight.Medium,
                fontSize = 12.sp,
                modifier = Modifier.padding(horizontal = 5.dp)
            )
        }
        Slider(
            limitNumber,
            onValueChange = {
                limitNumber = it
                GlobalSettings.isCardLimitEnabled = it != 0f
                GlobalSettings.cardNbLimit.value = (limitNumber * 10).roundToInt()
            },
            colors = SliderDefaults.colors(
                thumbColor = MaterialTheme.colors.secondary,
                activeTrackColor = MaterialTheme.colors.secondary,
                activeTickColor = MaterialTheme.colors.secondary
            ),
            modifier = Modifier
                .fillMaxWidth(.9f)
                .padding(top = 10.dp, bottom = 5.dp, start = 10.dp, end = 10.dp)
        )
    }
    Card(
        shape = RoundedCornerShape(10.dp),
        elevation = 4.dp,
        backgroundColor = MaterialTheme.colors.surface,
        modifier = Modifier.padding(vertical = 10.dp)
    ) {
        ExposedDropdownMenuBox(
            expanded = filterExpanded,
            onExpandedChange = { filterExpanded = !filterExpanded }
        ) {
            TextField(
                value = filterName,
                onValueChange = {},
                readOnly = true,
                trailingIcon = {
                    ExposedDropdownMenuDefaults.TrailingIcon(
                        expanded = filterExpanded
                    )
                },
                colors = ExposedDropdownMenuDefaults.textFieldColors(
                    textColor = MaterialTheme.colors.onSurface,
                    backgroundColor = MaterialTheme.colors.surface
                ),
                shape = RoundedCornerShape(5.dp),
                modifier = Modifier
                    .fillMaxWidth(.9f)
                    .padding(2.dp)
            )
            ExposedDropdownMenu(
                expanded = filterExpanded,
                onDismissRequest = { filterExpanded = false }
            ) {
                items.forEachIndexed { index, _ ->
                    DropdownMenuItem(
                        onClick = {
                            items = items.mapIndexed { j, item ->
                                if (index == j) {
                                    item.copy(isSelected = !item.isSelected)
                                } else item
                            }
                            GlobalSettings.handleToyKind(enumValues<ToyKind>()[index + 1])
                            filterName = GlobalSettings.getFilterName()
                        }
                    ) {
                        Text(text = items[index].name, modifier = Modifier.fillMaxWidth(.82f))
                        Spacer(modifier = Modifier.width(20.dp))
                        if (items[index].isSelected) {
                            Icon(
                                imageVector = Icons.Outlined.Check,
                                contentDescription = "Selected",
                                tint = Color.Green,
                                modifier = Modifier.size(20.dp)
                            )
                        }
                    }
                }
            }
        }
    }
    Card(
        shape = RoundedCornerShape(10.dp),
        elevation = 4.dp,
        backgroundColor = MaterialTheme.colors.surface,
        modifier = Modifier.padding(vertical = 10.dp)
    ) {
        Row(
            horizontalArrangement = Arrangement.SpaceBetween,
            verticalAlignment = Alignment.CenterVertically,
            modifier = Modifier
                .fillMaxWidth(.9f)
                .padding(2.dp)
        ) {
            Text("Fingerprint Lock", fontFamily = getPoppins(), fontWeight = FontWeight.Bold, fontSize = 12.sp, modifier = Modifier.padding(horizontal = 5.dp))
            Checkbox(
                checked = fingerProtection,
                onCheckedChange = onActivateFingerProtection
            )
        }
    }
}
